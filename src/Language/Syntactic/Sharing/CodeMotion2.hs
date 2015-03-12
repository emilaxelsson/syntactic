{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DoRec #-}
module Language.Syntactic.Sharing.CodeMotion2
    ( codeMotion2
    , reifySmart2
    ) where

import Control.Arrow
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Array
import Data.List
import Data.Maybe (fromJust,fromMaybe)
import Data.Function
import Data.Hash
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.SimpleCodeMotion

typeEq :: forall dom a b. (Typeable a, Typeable b) => ASTF dom a -> ASTF dom b -> Bool
typeEq a b | Just _ <- (gcast b :: Maybe (ASTF dom a)) = True
typeEq _ _ = False

isVariable :: PrjDict dom -> ASTF (NodeDomain dom) a -> Bool
isVariable pd (Sym (C' (InjR (prjVariable pd -> Just _)))) = True
isVariable pd _ = False

newtype NodeId = NodeId { nodeInteger :: Integer }
  deriving (Eq, Ord, Num, Real, Integral, Enum, Ix)

instance Show NodeId
  where
    show (NodeId i) = show i

showNode :: NodeId -> String
showNode n = "node:" ++ show n

instance AlphaEq dom dom dom env => AlphaEq Node Node dom env
  where
    alphaEqSym (Node n1) _ (Node n2) _ = return (n1 == n2)

instance Constrained Node
  where
    type Sat Node = Top
    exprDict _ = Dict

instance Equality Node
  where
    equal (Node n1) (Node n2) = error "can't compare nodes for equality"
    exprHash (Node n)         = hash (nodeInteger n)

-- | Placeholder for a syntax tree. Similar to Node from Graph, but with the
-- invariant that nodes with the same id are alpha-equivalent, given that they
-- come from the same expression.
data Node a
  where
    Node :: NodeId -> Node (Full a)

instance Render Node where
  renderSym (Node n) = showNode n


type NodeDomain dom = (Node :+: dom) :|| Sat dom

-- | A gathered sub-expression along with information used to decide where and
-- if it should be shared.
data Gathered dom = Gathered
    { geExpr :: ASTSAT (NodeDomain dom)
        -- ^ The gathered expression.
    , geNodeId :: NodeId
        -- ^ The node id of the expression.
    , geFreeVars :: Set.Set VarId
        -- ^ Variables that occur free in the expression.
    , geInfo :: [(NodeId, GatherInfo)]
        -- ^ A list of nodes which the gathered expression occurs in, which it
        -- should not be hoisted out of, along with the number of times it occurs
        -- in it and the union of all the scopes where the variable occurs.
    }


-- | An occurence count and a union of scopes for a gathered expression. Used
-- for the heuristic for when to share an expression.
data GatherInfo = GatherInfo
    { giCount :: Int
    , giScopes :: Set.Set VarId
    }
  deriving Show


newtype HashySet a = HashySet { unHashySet :: Map.Map Hash [a] }

lookupWithHS :: ([a] -> b) -> Hash -> HashySet a -> b
lookupWithHS f h (HashySet m) = case Map.lookup h m of
    Nothing -> f []
    Just as -> f as

updateWithHS :: (Maybe [a] -> Maybe [a]) -> Hash -> HashySet a -> HashySet a
updateWithHS f h (HashySet m) = HashySet $ Map.alter f h m

emptyHS = HashySet Map.empty

toListHS (HashySet m) = concatMap snd $ Map.toList m

-- | A set of expressions used to keep track of gathered expression in `gather`
type GatherSet dom = HashySet (Gathered dom)

lookupGS :: forall dom a
    .  ( AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , ConstrainedBy (NodeDomain dom) Typeable
       , Equality dom)
    => GatherSet dom
    -> ASTF (NodeDomain dom) a
    -> Maybe (Gathered dom)
lookupGS hs e = lookupWithHS look (exprHash e) hs
  where
    look :: [Gathered dom] -> Maybe (Gathered dom)
    look [] = Nothing
    look (g:gs) | ASTB ge <- geExpr g
                , Dict <- exprDictSub pTypeable ge
                , Dict <- exprDictSub pTypeable e
                , alphaEq ge e
                , typeEq ge e
                = Just g
    look (g:gs) = look gs

updateGS :: forall dom
    .  ( AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , ConstrainedBy (NodeDomain dom) Typeable
       , Equality dom)
    => GatherSet dom
    -> Gathered dom
    -> GatherSet dom
updateGS hs g
    | ASTB ge <- geExpr g
    = updateWithHS alt (exprHash ge) hs
  where
    alt :: Maybe [Gathered dom] -> Maybe [Gathered dom]
    alt (Just gs) = Just $ ins gs
    alt Nothing   = Just [g]
    ins :: [Gathered dom] -> [Gathered dom]
    ins [] = [g]
    ins (x:xs) | ASTB xe <- geExpr x
               , ASTB ge <- geExpr g
               , Dict <- exprDictSub pTypeable xe
               , Dict <- exprDictSub pTypeable ge
               , alphaEq xe ge
               , typeEq xe ge
               = g : xs
    ins (x:xs) = x : ins xs

emptyGS :: GatherSet dom
emptyGS = emptyHS

toListGS :: GatherSet dom -> [Gathered dom]
toListGS gs = toListHS gs

type RebuildEnv dom =
    ( Map.Map NodeId (ASTSAT dom)
        -- associates node ids with the AST they should be substituted by
    , Set.Set VarId
        -- bound variables
    , [NodeId]
        -- nodes that have been encountered
    )

type RebuildMonad dom m a = ReaderT (RebuildEnv dom) m a

runRebuild :: (MonadState VarId m) => RebuildMonad dom m a -> m a
runRebuild m = runReaderT m (Map.empty, Set.empty, [])

addBoundVar :: (Monad m) => VarId -> RebuildMonad dom m a -> RebuildMonad dom m a
addBoundVar v =  local (\(nm,vs,sn) -> (nm, Set.insert v vs, sn))

getBoundVars :: (Monad m) => RebuildMonad dom m (Set.Set VarId)
getBoundVars = do
    (_,bv,_) <- ask
    return bv

addNodeExpr :: (Monad m) => NodeId -> ASTSAT dom -> RebuildMonad dom m a -> RebuildMonad dom m a
addNodeExpr n a = local (\(nm,vs,sn) -> (Map.insert n a nm, vs, sn))

getNodeExprMap :: (Monad m) => RebuildMonad dom m (Map.Map NodeId (ASTSAT dom))
getNodeExprMap = do
    (nm,_,_) <- ask
    return nm

addSeenNode :: (Monad m) => NodeId -> RebuildMonad dom m a -> RebuildMonad dom m a
addSeenNode n = local (\(nm,vs,sn) -> (nm, vs, n:sn))

getSeenNodes :: (Monad m) => RebuildMonad dom m [NodeId]
getSeenNodes = do
    (_,_,sn) <- ask
    return sn



codeMotion2 :: forall dom m a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom dom [(VarId,VarId)]
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom
       , MonadState VarId m
       )
    => (forall c. ASTF dom c -> Bool)  -- ^ Control wether a sub-expression can be hoisted over the given expression
    -> PrjDict dom
    -> MkInjDict dom
    -> ASTF dom a
    -> m (ASTF dom a)
codeMotion2 hoistOver pd mkId a = rebuild pd mkId garr a'
  where
    (garr, a') = gather hoistOver pd a

type ShareInfo dom = (NodeId, ASTSAT (NodeDomain dom), GatherInfo)

rebuild :: forall dom m a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom
       , MonadState VarId m
       )
    => PrjDict dom
    -> MkInjDict dom
    -> Array NodeId (Gathered dom)
    -> ASTF (NodeDomain dom) a
    -> m (ASTF dom a)
rebuild pd mkId nodes (Sym (C' (InjL _))) = error "rebuild: root is a node"
rebuild pd mkId nodes a = runRebuild $ rebuild' 0 a
  where
    nodeExpr :: NodeId -> ASTSAT (NodeDomain dom)
    nodeExpr n = geExpr (nodes ! n)

    freeVars :: NodeId -> Set.Set VarId
    freeVars n = geFreeVars (nodes ! n)

    nodeDeps :: Array NodeId (Set.Set NodeId)
    nodeDeps = nodeDepsArray
      where
        nodeDepsArray = array (0,snd (bounds nodes)) [(n, nodeDepsNode n) | n <- 0 : indices nodes]

        nodeDepsNode :: NodeId -> Set.Set NodeId
        nodeDepsNode 0 = nodeDepsExp a
        nodeDepsNode n = liftASTB nodeDepsExp $ geExpr (nodes ! n)

        nodeDepsExp :: AST (NodeDomain dom) b -> Set.Set NodeId
        nodeDepsExp (Sym (C' (InjR _))) = Set.empty
        nodeDepsExp (Sym (C' (InjL (Node n)))) = Set.insert n (nodeDepsArray ! n)
        nodeDepsExp (s :$ b) = Set.union (nodeDepsExp s) (nodeDepsExp b)

    -- | Computes a list of nodes that should be considered for sharing at a
    -- particular node. Must return a ShareInfo corresponding to any node
    -- that might be encounter in direct sub-expression of the node that has
    -- not already been considered at a parent node. Otherwise we will not know
    -- what to do with that node.
    -- Implementation is pretty bizarre right now, but it should be replaced anyway.
    nodesToConsider :: NodeId -> (NodeId -> Bool) -> Set.Set VarId -> [NodeId] -> [ShareInfo dom]
    nodesToConsider n f bv seenNodes = concatMap mkShareInfo (map (\n -> (n, nodes ! n)) (Set.elems (nodeDeps ! n)))
      where
        maximumBy' f [] = []
        maximumBy' f xs = [maximumBy f xs]

        mkShareInfo (n,g) = map snd $ filter ((/=Nothing) . fst) $ maximumBy' (compare `on` fst)
            [ (elemIndex il seenNodes, (n, geExpr g, gi))
            | (il,gi) <- geInfo g
            , Set.null (freeVars n `Set.difference` bv)
                -- any free variables in the sub-expression must be bound
            , il /= n
                -- this case handled separately
            , f n
            ]

    -- Nodes which has the given node as its inner limit.
    unshareableNodes :: NodeId -> AST (NodeDomain dom) b -> [ShareInfo dom]
    unshareableNodes n (Sym s) = []
    unshareableNodes n (s :$ Sym (C' (InjL (Node n'))))
        | Just gi <- lookup n (geInfo (nodes ! n'))
        = (n', geExpr (nodes ! n'), gi) : unshareableNodes n s
        | Just gi <- lookup n' (geInfo (nodes ! n'))
        = (n', geExpr (nodes ! n'), gi) : unshareableNodes n s
    unshareableNodes n (b :$ s) = unshareableNodes n b

    unshareable2Nodes :: Maybe VarId -> ASTF (NodeDomain dom) b -> [ShareInfo dom]
    unshareable2Nodes Nothing  _ = []
    unshareable2Nodes (Just v) a = go a []
      where
        go :: AST (NodeDomain dom) c -> [ShareInfo dom] -> [ShareInfo dom]
        go (Sym s) l = l
        go (s :$ Sym (C' (InjL (Node n')))) l
            | Set.member v (freeVars n') = go s ((n', geExpr (nodes ! n'), undefined):l)
            | otherwise                  = go s l

    rebuild' :: forall b
        .  NodeId
        -> ASTF (NodeDomain dom) b
        -> RebuildMonad dom m (ASTF dom b)
    rebuild' n a@(Sym (C' (InjR lam)) :$ ns@(Sym (C' (InjL (Node nb)))))
        | Just v <- prjLambda pd lam
        = addSeenNode n $ shareExprsIn (Just v) n a
    rebuild' n (Sym (C' (InjR s))) = return $ Sym s
    rebuild' n a = addSeenNode n $ shareExprsIn Nothing n a

    shareExprsIn :: forall b
        .  Maybe VarId -- if the last argument is a lambda, this contains the lambda VarId, otherwise Nothing.
        -> NodeId
        -> ASTF (NodeDomain dom) b
        -> RebuildMonad dom m (ASTF dom b)
    shareExprsIn mlv n a = do
        bv <- getBoundVars
        seenNodes <- getSeenNodes
        nodeMap <- getNodeExprMap
        let considered = nodesToConsider n (\n' -> n' /= n && not (Map.member n' nodeMap) && Set.member n' (nodeDeps ! n)) bv seenNodes
        let sorted = sortBy (compare `on` (\(n,_,_) -> n)) considered
        let unshareable = nubBy ((==) `on` (\(n,_,_) -> n)) $ unshareableNodes n a ++ unshareable2Nodes mlv a
        unshare mlv unshareable $ shareEm mlv sorted a

    unshare :: Maybe VarId -> [ShareInfo dom] -> RebuildMonad dom m b -> RebuildMonad dom m b
    unshare mlv []     m = m
    unshare mlv ((n, ASTB b, gi):sis) m = do
          b' <- rebuildMaybeUnderLambda mlv n b
          addNodeExpr n (ASTB b') $ unshare mlv sis m

    shareEm
        :: Maybe VarId
        -> [ShareInfo dom]
        -> ASTF (NodeDomain dom) b
        -> RebuildMonad dom m (ASTF dom b)
    shareEm mlv [] a = fixNodeExprSub a
    shareEm mlv ((n, ASTB b, gi) : sis) a = do
        bv <- getBoundVars
        case mkId (inlineAll nodeExpr b) (inlineAll nodeExpr a) of
            Just id | heuristic bv gi b -> do
                b' <- rebuild' n b
                v <- get; put (v+1)
                a' <- addNodeExpr n (ASTB (Sym (injVariable id v))) $ shareEm mlv sis a
                return $ Sym (injLet id) :$ b' :$ (Sym (injLambda id v) :$ a')
            _ -> do
                b' <- rebuildMaybeUnderLambda mlv n b
                a' <- addNodeExpr n (ASTB b') $ shareEm mlv sis a
                return a'

    rebuildMaybeUnderLambda
        :: Maybe VarId
        -> NodeId
        -> ASTF (NodeDomain dom) b
        -> RebuildMonad dom m (ASTF dom b)
    rebuildMaybeUnderLambda (Just lv) n a = addBoundVar lv $ rebuild' n a
    rebuildMaybeUnderLambda Nothing   n a = rebuild' n a

    fixNodeExprSub :: forall b
        .  ( ConstrainedBy dom Typeable
           , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
           , Equality dom
           )
        => AST (NodeDomain dom) b
        -> RebuildMonad dom m (AST dom b)
    fixNodeExprSub (Sym (C' (InjR s))) = return (Sym s)
    fixNodeExprSub (s :$ b) = do
        b' <- fixNodeExpr b
        s' <- fixNodeExprSub s
        return (s' :$ b')

    fixNodeExpr :: forall b
                .  ASTF (NodeDomain dom) b -> RebuildMonad dom m (ASTF dom b)
    fixNodeExpr (ns@(Sym (C' (InjL (Node n))))) = do
        nodeMap <- getNodeExprMap
        let a = lookNode nodeMap
        return a
      where
        lookNode nodeMap = case Map.lookup n nodeMap of
            Just (ASTB a)
                | Dict <- exprDictSub pTypeable ns
                , Dict <- exprDictSub pTypeable a
                -> case gcast a of
                    Nothing -> error "rebuild: type mismatch"
                    Just a -> a
            Nothing -> error ("rebuild: lost node: " ++ show n)

    heuristic :: Set.Set VarId -> GatherInfo -> ASTF (NodeDomain dom) b -> Bool
    heuristic bv gi b = not (isVariable pd b) && (giCount gi > 1 || not (Set.null (giScopes gi `Set.difference` bv)))

inlineAll :: forall dom a
    .  ConstrainedBy dom Typeable
    => (NodeId -> ASTSAT (NodeDomain dom))
    -> ASTF (NodeDomain dom) a
    -> ASTF dom a
inlineAll nodes a = go a
  where
    go :: AST (NodeDomain dom) sig -> AST dom sig
    go (s :$ a) = go s :$ go a
    go (Sym (C' (InjR s))) = Sym s
    go s@(Sym (C' (InjL (Node n)))) = case nodes n of
        ASTB a
          | Dict <- exprDictSub pTypeable s
          , Dict <- exprDictSub pTypeable a
          -> case gcast a of
              Nothing -> error "inlineAll: type mismatch"
              Just a  -> go a


type GatherEnv =
    ( [NodeId]
        -- List of nodes upwards in the syntax tree that cannot be hoisted over
    , Set.Set VarId
        -- Varibles in scope
    )

type Additional = Map.Map NodeId [(NodeId, GatherInfo)]

data GatherState dom = GatherState
    { gatherSet :: GatherSet dom -- Set of expressions that have been recorded
    , nodeCounter :: NodeId
    , lambdaTable :: LambdaTable dom
    , additionals :: Map.Map NodeId [(NodeId, GatherInfo)]
    }

data LambdaInfo dom = LambdaInfo
    { liExpr :: ASTSAT dom
    , liLambdaNodeId :: NodeId
    , liFreeVars :: Set.Set VarId
    }

type GatherMonad dom a = RWS GatherEnv (Set.Set VarId) (GatherState dom) a

runGather :: GatherMonad dom a -> (GatherState dom, a)
runGather gather = (s', a)
  where
    (a,s',w) = runRWS gather ([0], Set.empty) (GatherState emptyGS 1 emptyHS Map.empty)

type LambdaTable dom = HashySet (LambdaInfo dom)

lookupLT :: forall dom a
    . ( AlphaEq dom dom dom [(VarId,VarId)]
      , Equality dom)
    => Hash
    -> ASTF dom a
    -> LambdaTable dom
    -> Maybe (LambdaInfo dom)
lookupLT h e t = lookupWithHS look h t
  where
    look :: [LambdaInfo dom] -> Maybe (LambdaInfo dom)
    look [] = Nothing
    look (li:xs) | liftASTB alphaEq (liExpr li) e
                 = Just li
    look (x:xs) = look xs

-- | Note: Assumes the given lambda is not already in the map
insertLT :: forall dom a
    . ( Sat dom a
      , AlphaEq dom dom dom [(VarId,VarId)]
      , Equality dom)
    => Hash
    -> ASTF dom a
    -> NodeId
    -> Set.Set VarId
    -> LambdaTable dom
    -> LambdaTable dom
insertLT h e n fv t = updateWithHS ins h t
  where
    ins :: Maybe [LambdaInfo dom] -> Maybe [LambdaInfo dom]
    ins (Just xs) = Just (LambdaInfo (ASTB e) n fv : xs)
    ins Nothing = Just [LambdaInfo (ASTB e) n fv]


getInnerLimit :: GatherMonad dom NodeId
getInnerLimit = liftM (head . fst) ask

getScope :: GatherMonad dom (Set.Set VarId)
getScope = liftM snd ask

getLambdaTable :: GatherMonad dom (LambdaTable dom)
getLambdaTable = liftM lambdaTable get

putLambdaTable :: LambdaTable dom -> GatherMonad dom ()
putLambdaTable lt = do
    st <- get
    put (st { lambdaTable = lt })

addInnerLimit :: NodeId -> GatherMonad dom a -> GatherMonad dom a
addInnerLimit n = local (\(ns,vs) -> (n:ns,vs))

addScopeVar :: VarId -> GatherMonad dom a -> GatherMonad dom a
addScopeVar v = censor (Set.delete v) . local (\(ns,vs) -> (ns, Set.insert v vs ))

-- | Convert an expression to a graph representation where each set of
-- alpha-equivalent sub-expressions share a node. Occurence counts for the
-- sub-expressions, and other information is also recorded.
gather :: forall dom a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , AlphaEq dom dom dom [(VarId,VarId)]
       , Equality dom
       )
    => (forall c. ASTF dom c -> Bool)
    -> PrjDict dom
    -> ASTF dom a
    -> (Array NodeId (Gathered dom), ASTF (NodeDomain dom) a)
gather hoistOver pd a@(Sym s) | Dict <- exprDict a = (array (1,0) [], Sym (C' (InjR s)))
gather hoistOver pd a = (gatheredArr, a')
  where
    (st,a') | Dict <- exprDict a = runGather (gatherRoot a)

    gatherRoot :: ASTF dom b -> GatherMonad dom (ASTF (NodeDomain dom) b)
    gatherRoot a@(Sym lam :$ _) | Just v <- prjLambda pd lam
                                , Dict <- exprDict a
                                = addScopeVar v $ gatherRec (hoistOver a) a
    gatherRoot a | Dict <- exprDict a = gatherRec (hoistOver a) a

    gths = toListGS (gatherSet st)

    idx = map geNodeId gths

    adArr :: Array NodeId [(NodeId, GatherInfo)]
    adArr = accumArray (++) []
        (1, nodeCounter st - 1)
        ((Map.assocs (additionals st)) ++ [(n, []) | n <- [1..(nodeCounter st - 1)]])

    preGatheredArr :: Array NodeId (Gathered dom)
    preGatheredArr = array
        (1, nodeCounter st - 1)
        (zip idx gths)

    gatheredArr :: Array NodeId (Gathered dom)
    gatheredArr = array
        (1, nodeCounter st - 1)
        (zip idx (Prelude.map withAdditionals gths))

    withAdditionals g = g { geInfo = info}
      where
        info = mergeInfos
                (geInfo g)
                (Map.findWithDefault [] (geNodeId g) propagateAdditionals)

    propagateAdditionals :: Additional
    propagateAdditionals = foldr propAdditional (additionals st) $ Map.toDescList (additionals st)
      where
        propAdditional :: (NodeId, [(NodeId, GatherInfo)]) -> Additional -> Additional
        propAdditional (n, gi) ad = propAdditionalNode n gi ad

        propAdditionalNode :: NodeId -> [(NodeId, GatherInfo)] -> Additional -> Additional
        propAdditionalNode n gi ad = liftASTB (propAdditionalExpr n gi) (geExpr (preGatheredArr ! n)) ad

        propAdditionalExpr :: NodeId -> [(NodeId, GatherInfo)] -> AST (NodeDomain dom) b -> Additional -> Additional
        propAdditionalExpr n gi (Sym s) ad = ad
        propAdditionalExpr n gi (s :$ Sym (C' (InjL (Node n')))) ad = ad3
          where
            ad1 = Map.insertWith mergeInfos n' gi ad
            ad2 = propAdditionalNode n' gi ad1
            ad3 = propAdditionalExpr n gi s ad2

    applyAdditionals :: [(NodeId, GatherInfo)] -> Gathered dom -> Gathered dom
    applyAdditionals ad g = g { geInfo = mergeInfos ad (geInfo g) }

    varHash :: Map.Map VarId Hash
    varHash = lambdaHashes pd a

    gather'
        :: Bool
        -> ASTF dom b
        -> GatherMonad dom (ASTF (NodeDomain dom) b)
    gather' h a@(Sym lam :$ _) | Just v <- prjLambda pd lam
                               , Dict <- exprDict a = do
        lt <- getLambdaTable
        let hash = fromJust (Map.lookup v varHash)
        case lookupLT hash a lt of
            Just li -> do
                let n = liLambdaNodeId li
                anotherCopyOf n
                tell (liFreeVars li)
                return $ Sym $ C' $ InjL $ Node $ n
            Nothing -> do
                rec
                    (a',fv) <- listen $ addInnerLimitIf (not h) n $ addScopeVar v $ gatherRec (hoistOver a) a
                    n <- addInnerLimitIf (not h) n $ recordExpr fv a'
                putLambdaTable (insertLT hash a n fv lt)
                return $ Sym $ C' $ InjL $ Node n
    gather' h a | Dict <- exprDict a = do
        rec
            (a',fv) <- listen $ addInnerLimitIf (not h) n $ gatherRec (hoistOver a) a
            n <- addInnerLimitIf (not h) n $ recordExpr fv a'
        return $ Sym $ C' $ InjL $ Node n

    addInnerLimitIf True n m = addInnerLimit n m
    addInnerLimitIf _    n m = m

    gatherRec
        :: (Sat dom (DenResult b))
        => Bool
        -> AST dom b
        -> GatherMonad dom (AST (NodeDomain dom) b)
    gatherRec h (Sym var) | Just v <- prjVariable pd var = do
            tell (Set.singleton v)
            return $ Sym $ C' $ InjR var
    gatherRec h (Sym s) = return $ Sym $ C' $ InjR s
    gatherRec h (s :$ b) | Dict <- exprDict b = do
        b' <- gather' h b
        s' <- gatherRec h s
        return (s' :$ b')

    anotherCopyOf :: NodeId -> GatherMonad dom ()
    anotherCopyOf n = do
        st <- get
        let s = gatherSet st
        let ad = additionals st
        innerLimit <- getInnerLimit
        scope <- getScope
        put (st { additionals = Map.insertWith mergeInfos n [(innerLimit, GatherInfo 1 scope)] ad })

    recordExpr :: Set.Set VarId -> ASTF (NodeDomain dom) b -> GatherMonad dom NodeId
    recordExpr fv a | Dict <- exprDict a = do
        st <- get
        let s = gatherSet st
        let n = nodeCounter st
        innerLimit <- getInnerLimit
        scope <- getScope
        case lookupGS s a of
            Just ge -> do
                let ge' = ge { geInfo = updateInfo innerLimit (GatherInfo 1 scope) (geInfo ge) }
                put (st { gatherSet = updateGS s ge' })
                return (geNodeId ge)
            Nothing -> do
                let ge = Gathered { geExpr = ASTB a , geNodeId = n , geFreeVars = fv , geInfo = [(innerLimit, GatherInfo { giCount = 1 , giScopes = scope })] }
                put (st { gatherSet = updateGS s ge, nodeCounter = n+1 })
                return n

mergeInfos :: [(NodeId, GatherInfo)] -> [(NodeId, GatherInfo)] -> [(NodeId, GatherInfo)]
mergeInfos [] ys = ys
mergeInfos (x:xs) ys = mergeInfos xs (uncurry updateInfo x ys)

updateInfo :: NodeId -> GatherInfo -> [(NodeId, GatherInfo)] -> [(NodeId, GatherInfo)]
updateInfo il gi [] = [(il, gi)]
updateInfo il (GatherInfo c scope) ((n,gi):xs) | n == il = (n, gi') : xs
  where
    gi' = gi { giCount = giCount gi + c , giScopes = Set.union (giScopes gi) scope }
updateInfo il gi (x:xs) = x : updateInfo il gi xs


lambdaHashes :: forall dom a
    .  (Equality dom)
    => PrjDict dom
    -> ASTF dom a
    -> Map.Map VarId Hash
lambdaHashes pd a = execWriter (lambdaHashes' a)
  where
    lambdaHashes' :: AST dom b -> Writer (Map.Map VarId Hash) Hash
    lambdaHashes' (Sym lam :$ b) | Just v <- prjLambda pd lam = do
        h' <- lambdaHashes' b
        tell (Map.singleton v h')
        return $ hashInt 1 `combine` exprHash (Sym lam) `combine` h'
    lambdaHashes' (s :$ b) = do
        hs <- lambdaHashes' s
        hb <- lambdaHashes' b
        return $ hashInt 1 `combine` hs `combine` hb
    lambdaHashes' s = return $ hashInt 0 `combine` exprHash s

-- | Like 'reify' but with common sub-expression elimination and variable hoisting
reifySmart2 :: forall dom p pVar a
    .  ( AlphaEq dom dom (NodeDomain (FODomain dom p pVar)) [(VarId,VarId)]
       , AlphaEq dom dom (FODomain dom p pVar) [(VarId,VarId)]
       , Equality dom
       , Syntactic a
       , Domain a ~ HODomain dom p pVar
       , p :< Typeable
       )
    => (forall c. ASTF (FODomain dom p pVar) c -> Bool)
    -> MkInjDict (FODomain dom p pVar)
    -> a
    -> ASTF (FODomain dom p pVar) (Internal a)
reifySmart2 hoistOver mkId = flip evalState 0 . (codeMotion2 hoistOver prjDictFO mkId <=< reifyM . desugar)
