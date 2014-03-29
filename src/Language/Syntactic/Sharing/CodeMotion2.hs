{-# LANGUAGE UndecidableInstances #-}
module Language.Syntactic.Sharing.CodeMotion2 
    ( codeMotion2
    , reifySmart2
    ) where

import Control.Monad.State
import Control.Monad.Reader
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


type NodeDomain dom = (Node :+: dom) :|| Sat dom


-- | A gathered sub-expression along with information used to decide where and
-- if it should be shared.
data Gathered dom = Gathered
    { geExpr :: ASTSAT (NodeDomain dom)
        -- ^ The gathered expression.
    , geNodeId :: NodeId
        -- ^ The node id of the expression.
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

-- | A set of expressions used to keep track of gathered expression in `gather`
newtype GatherSet dom = GatherSet {unGatherSet :: Map.Map Hash [Gathered dom]}
        

lookupGS :: forall dom a 
    .  ( AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom)
    => GatherSet dom
    -> ASTF (NodeDomain dom) a
    -> Maybe (Gathered dom)
lookupGS (GatherSet m) e = Map.lookup (exprHash e) m >>= look
  where 
    look :: [Gathered dom] -> Maybe (Gathered dom)
    look [] = Nothing
    look (g:gs) | ASTB ge <- geExpr g
                , alphaEq ge e
                = Just g
    look (g:gs) = look gs

updateGS :: forall dom
    .  ( AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom)
    => GatherSet dom
    -> Gathered dom
    -> GatherSet dom
updateGS (GatherSet m) g
    | ASTB ge <- geExpr g
    = GatherSet $ Map.alter alt (exprHash ge) m
  where
    alt :: Maybe [Gathered dom] -> Maybe [Gathered dom]
    alt (Just gs) = Just $ ins gs
    alt Nothing   = Just [g]
    ins :: [Gathered dom] -> [Gathered dom]
    ins [] = [g]
    ins (x:xs) | ASTB xe <- geExpr x
                , ASTB ge <- geExpr g
                , alphaEq xe ge
                = g : xs
    ins (x:xs) = x : ins xs

emptyGS = GatherSet $ Map.empty

toListGS (GatherSet m) = concatMap snd (Map.toList m)

type RebuildEnv dom = 
    ( Map.Map NodeId (ASTSAT dom)
        -- ^ associates node ids with the AST they should be substituted by
    , Set.Set VarId
        -- ^ bound variables
    , [NodeId]
        -- ^ nodes that have been encountered
    )
  
type RebuildMonad dom a = ReaderT (RebuildEnv dom) (State VarId) a


runRebuild :: RebuildMonad dom a -> State VarId a
runRebuild m = runReaderT m (Map.empty, Set.empty, [0])

addBoundVar :: VarId -> RebuildMonad dom a -> RebuildMonad dom a
addBoundVar v =  local (\(nm,vs,sn) -> (nm, Set.insert v vs, sn))

getBoundVars :: RebuildMonad dom (Set.Set VarId)
getBoundVars = do
    (_,bv,_) <- ask
    return bv

addNodeExpr :: NodeId -> ASTSAT dom -> RebuildMonad dom a -> RebuildMonad dom a
addNodeExpr n a = local (\(nm,vs,sn) -> (Map.insert n a nm, vs, sn))

getNodeExprMap :: RebuildMonad dom (Map.Map NodeId (ASTSAT dom))
getNodeExprMap = do
    (nm,_,_) <- ask
    return nm

addSeenNode :: NodeId -> RebuildMonad dom a -> RebuildMonad dom a
addSeenNode n = local (\(nm,vs,sn) -> (nm, vs, n:sn))

getSeenNodes :: RebuildMonad dom [NodeId]
getSeenNodes = do
    (_,_,sn) <- ask
    return sn



codeMotion2 :: forall dom a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom
       )
    => (forall c. ASTF dom c -> Bool)  -- ^ Control wether a sub-expression can be hoisted over the given expression
    -> PrjDict dom
    -> MkInjDict dom
    -> ASTF dom a
    -> State VarId (ASTF dom a)
codeMotion2 hoistOver pd mkId a = do
    let (gm, a') = gather hoistOver pd a
    rebuild pd mkId (toListGS gm) a'

type ShareInfo dom = (NodeId, ASTSAT (NodeDomain dom), GatherInfo)

data ShareMaybe dom a
  where
    Share :: Sat dom b => VarId -> InjDict dom b a -> ASTF dom b -> ShareMaybe dom a
    Not :: Sat dom b => ASTF dom b -> ShareMaybe dom a

rebuild :: forall dom a
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom
       )
    => PrjDict dom
    -> MkInjDict dom
    -> [Gathered dom]
    -> ASTF (NodeDomain dom) a
    -> State VarId (ASTF dom a)
rebuild pd mkId gs (Sym (C' (InjL _))) = error ""
rebuild pd mkId gs a = runRebuild $ rebuild' 0 a
  where
    nodes :: Array NodeId (Gathered dom)
    nodes = array
        (1, maximum (0:(Prelude.map geNodeId gs)))
        (zip (Prelude.map geNodeId gs) gs)

    freeVars :: Array NodeId (Set.Set VarId)
    freeVars = nodesFreeVars pd nodes

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
    nodesToConsider :: (NodeId -> Bool) -> Set.Set VarId -> [NodeId] -> [ShareInfo dom]
    nodesToConsider f bv seenNodes = concatMap mkShareInfo (assocs nodes)
      where
        maximumBy' f [] = []
        maximumBy' f xs = [maximumBy f xs]
        mkShareInfo (n,g) = map snd $ maximumBy' (compare `on` fst) $ map (\(Just i,x) -> (i,x)) $ filter ((/=Nothing) . fst)
            [ (elemIndex il seenNodes, (n, geExpr g, gi))
            | (il,gi) <- geInfo g
            --, i <- elemIndex il seenNodes
                -- must be shared inside `il`
            , Set.null (freeVars ! n `Set.difference` bv)
                -- any free variables in the sub-expression must be bound
            , f n
            ]
    
    rebuild' :: forall b
        .  NodeId
        -> ASTF (NodeDomain dom) b
        -> RebuildMonad dom (ASTF dom b)
    rebuild' n (a@(Sym (C' (InjR lam)) :$ _))
        | Just v <- prjLambda pd lam 
        = do
            a' <- addBoundVar v $ shareExprsIn n (addBoundVar v (fixNodeExprSub a))
            return a'
    rebuild' n (Sym (C' (InjR s))) = return $ Sym s
    rebuild' n a = shareExprsIn n (fixNodeExprSub a)
    
    shareExprsIn :: forall b
        .  NodeId
        -> RebuildMonad dom (ASTF dom b)
        -> RebuildMonad dom (ASTF dom b)
    shareExprsIn n ma = do
        bv <- getBoundVars
        seenNodes <- getSeenNodes
        nodeMap <- getNodeExprMap
        let considered = nodesToConsider (\n' -> n' /= n && not (Map.member n' nodeMap) && Set.member n' (nodeDeps ! n)) bv seenNodes
        let (share,notShare) = partition (\(_,(ASTB a),gi) -> heuristic bv gi a) considered
        let sortedShare = sortBy (compare `on` (\(n,_,_) -> n)) share
        (ms, a') <- addSeenNode n $ unShareNodes notShare (mfix (shareEm [] sortedShare ma))
        return (letBindMaybeShares ms a')

    letBindMaybeShares :: [ShareMaybe dom b] -> ASTF dom b -> ASTF dom b
    letBindMaybeShares ms a = foldl letBindMaybeShare a ms
      where
        letBindMaybeShare a (Share v id b) = Sym (injLet id) :$ b :$ (Sym (injLambda id v) :$ a)
        letBindMaybeShare a (Not b) = a

    unShareNodes :: [ShareInfo dom] -> RebuildMonad dom b -> RebuildMonad dom b
    unShareNodes sis m = foldr unShareNode m sis
      where
        unShareNode (n,(ASTB b),_) m = do
            b' <- rebuild' n b
            addNodeExpr n (ASTB b') m
    
    shareEm
        :: [(NodeId,ShareMaybe dom b)]
        -> [ShareInfo dom] 
        -> RebuildMonad dom (ASTF dom b)
        -> ([ShareMaybe dom b], ASTF dom b)
        -> RebuildMonad dom ([ShareMaybe dom b], ASTF dom b)
    shareEm env [] ma _ = do
        a <- addMaybeShares env ma
        return $ (map snd env, a)
    shareEm env ((n, ASTB b, gi) : sis) ma ~(shs,a) = do
        b' <- addMaybeShares env $ rebuild' n b
        v <- get; put (v+1)
        shareEm ((n, mkShareMaybe v a b') : env) sis ma (shs,a)

    addMaybeShares :: [(NodeId, ShareMaybe dom b)] -> RebuildMonad dom c -> RebuildMonad dom c
    addMaybeShares [] m = m
    addMaybeShares ((n,ms):xs) m = addNodeExpr n (exprFromMaybeShare ms) $ addMaybeShares xs m

    exprFromMaybeShare :: ShareMaybe dom b -> ASTSAT dom
    exprFromMaybeShare (Share v id b) = ASTB $ Sym $ injVariable id v
    exprFromMaybeShare (Not b)        = ASTB b

    mkShareMaybe :: Sat dom c => VarId -> ASTF dom b -> ASTF dom c -> ShareMaybe dom b
    mkShareMaybe v a b | Just id <- mkId b a = Share v id b
    mkShareMaybe _ _ b = Not b
    

    fixNodeExprSub :: forall b
        .  ( ConstrainedBy dom Typeable
           , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
           , Equality dom
           )
        => AST (NodeDomain dom) b
        -> RebuildMonad dom (AST dom b)
    fixNodeExprSub (Sym (C' (InjR s))) = return (Sym s)
    fixNodeExprSub (s :$ b) = do
        b' <- fixNodeExpr b
        s' <- fixNodeExprSub s
        return (s' :$ b')
        
    fixNodeExpr :: forall b . ASTF (NodeDomain dom) b -> RebuildMonad dom (ASTF dom b)
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
            Nothing -> error "rebuild: lost node"


    heuristic :: Set.Set VarId -> GatherInfo -> ASTF (NodeDomain dom) b -> Bool
    heuristic bv gi b = not (isVariable pd b) && (giCount gi > 1 || not (Set.null (giScopes gi `Set.difference` bv)))

-- | Given a array of nodes calculates the set of free variables in the
-- sub-expression each 
nodesFreeVars :: forall dom
    .  PrjDict dom 
    -> Array NodeId (Gathered dom) 
    -> Array NodeId (Set.Set VarId)
nodesFreeVars pd nodes = freeVars
  where
    freeVars = array (bounds nodes) [(n, freeVarsNode n) | n <- indices nodes]

    freeVarsNode :: NodeId -> Set.Set VarId
    freeVarsNode n = liftASTB freeVarsExp $ geExpr (nodes ! n)
    
    freeVarsExp :: AST (NodeDomain dom) a -> Set.Set VarId
    freeVarsExp (Sym (C' (InjR var))) | Just v <- prjVariable pd var = Set.singleton v
    freeVarsExp (Sym (C' (InjR lam)) :$ b) | Just v <- prjLambda pd lam = Set.delete v (freeVarsExp b)
    freeVarsExp (Sym (C' (InjR _))) = Set.empty
    freeVarsExp (Sym (C' (InjL (Node n)))) = freeVars ! n
    freeVarsExp (s :$ b) = Set.union (freeVarsExp s) (freeVarsExp b)


type GatherEnv = 
    ( [NodeId]    
        -- ^ List of nodes upwards in the syntax tree that cannot be hoisted over
    , Set.Set VarId
        -- ^ Varibles in scope
    )
type GatherState dom = 
    ( GatherSet dom -- ^ Set of expressions that have been recorded
    , NodeId -- ^ Node counter.
    )

type GatherMonad dom a = ReaderT GatherEnv (State (GatherState dom)) a

runGather :: GatherSet dom -> GatherMonad dom a -> (GatherSet dom, a)
runGather s gather = (gm,a)
  where 
    (a,(gm,n')) = runState (runReaderT gather ([0], Set.empty)) (s,1)

getInnerLimit :: GatherMonad dom NodeId
getInnerLimit = liftM (head . fst) ask

getScope :: GatherMonad dom (Set.Set VarId)
getScope = liftM snd ask

addInnerLimit :: NodeId -> GatherMonad dom a -> GatherMonad dom a
addInnerLimit n = local (\(ns,vs) -> (n:ns,vs))

addScopeVar :: VarId -> GatherMonad dom a -> GatherMonad dom a
addScopeVar v = local (\(ns,vs) -> (ns, Set.insert v vs ))

-- | Convert an expression to a graph representation where each set of
-- alpha-equivalent sub-expressions share a node. Occurence counts for the
-- sub-expressions, and other information is also recorded.
gather :: forall dom a 
    .  ( ConstrainedBy dom Typeable
       , AlphaEq dom dom (NodeDomain dom) [(VarId,VarId)]
       , Equality dom
       )
    => (forall c. ASTF dom c -> Bool)
    -> PrjDict dom
    -> ASTF dom a
    -> (GatherSet dom, ASTF (NodeDomain dom) a)
gather hoistOver pd a@(Sym s) | Dict <- exprDict a = (emptyGS, Sym (C' (InjR s)))
gather hoistOver pd a | Dict <- exprDict a
                           = runGather emptyGS (gatherRec (hoistOver a) a)
  where
    gather' :: Bool -> ASTF dom b -> GatherMonad dom (ASTF (NodeDomain dom) b)
    gather' h a | Dict <- exprDict a = do
        (a',n) <-
          mfix (\(~(a',n)) -> do
            a' <- if h
                then gatherRec (hoistOver a) a 
                else addInnerLimit n $ gatherRec (hoistOver a) a
            n <- recordExpr a'
            return (a',n)
          )
        return $ Sym $ C' $ InjL $ Node n

    gatherRec 
        :: (Sat dom (DenResult b))
        => Bool
        -> AST dom b
        -> GatherMonad dom (AST (NodeDomain dom) b) 
    gatherRec h (Sym lam :$ b) | Just v <- prjLambda pd lam = do
        b' <- addScopeVar v $ gather' h b
        return ((Sym (C' (InjR lam))) :$ b')
    gatherRec h (Sym s) = return $ Sym $ C' $ InjR s
    gatherRec h (s :$ b) = do
        b' <- gather' h b
        s' <- gatherRec h s
        return (s' :$ b')

    recordExpr :: ASTF (NodeDomain dom) b -> GatherMonad dom NodeId
    recordExpr a | Dict <- exprDict a = do
        (s,n) <- get
        innerLimit <- getInnerLimit
        scope <- getScope
        case lookupGS s a of
            Just ge -> do
                let ge' = ge { geInfo = updateInfo scope (geInfo ge) innerLimit }
                put (updateGS s ge', n)
                return (geNodeId ge)
            Nothing -> do
                let ge = Gathered { geExpr = ASTB a , geNodeId = n , geInfo = [(innerLimit, GatherInfo { giCount = 1 , giScopes = scope })] }
                put (updateGS s ge, n+1)
                return n

updateInfo :: Set.Set VarId -> [(NodeId, GatherInfo)] -> NodeId -> [(NodeId, GatherInfo)]
updateInfo scope [] n = [(n, GatherInfo { giCount = 1 , giScopes = scope })]
updateInfo scope ((n,gi):xs) n' | n == n' = (n, gi') : xs
  where
    gi' = gi { giCount = giCount gi + 1 , giScopes = Set.union (giScopes gi) scope }
updateInfo scope (x:xs) n' = x : updateInfo scope xs n'


-- | Like 'reify' but with common sub-expression elimination and variable hoisting
reifySmart2 :: forall dom p pVar a
    .  ( AlphaEq dom dom (NodeDomain (FODomain dom p pVar)) [(VarId,VarId)]
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
