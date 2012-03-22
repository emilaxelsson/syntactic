{-# LANGUAGE UndecidableInstances #-}

-- | Representation and manipulation of abstract syntax graphs

module Language.Syntactic.Sharing.Graph where



import Control.Arrow ((***))
import Control.Monad.Reader
import Data.Array
import Data.Function
import Data.List
import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Sharing.Utils



--------------------------------------------------------------------------------
-- * Representation
--------------------------------------------------------------------------------

-- | Node identifier
newtype NodeId = NodeId { nodeInteger :: Integer }
  deriving (Eq, Ord, Num, Real, Integral, Enum, Ix)



-- | Placeholder for a syntax tree
data Node ctx a
  where
    Node :: Sat ctx a => NodeId -> Node ctx (Full a)

instance Show NodeId
  where
    show (NodeId i) = show i

showNode :: NodeId -> String
showNode n = "node:" ++ show n



instance WitnessCons (Node ctx)
  where
    witnessCons (Node _) = ConsWit

instance Render (Node ctx)
  where
    render (Node a) = showNode a

instance ToTree (Node ctx)



-- | An 'ASTF' with hidden result type
data SomeAST dom
  where
    SomeAST :: Typeable a => ASTF dom a -> SomeAST dom



-- | Environment for alpha-equivalence
class NodeEqEnv dom a
  where
    prjNodeEqEnv :: a -> NodeEnv dom
    modNodeEqEnv :: (NodeEnv dom -> NodeEnv dom) -> (a -> a)

type EqEnv dom = ([(VarId,VarId)], NodeEnv dom)

type NodeEnv dom =
    ( Array NodeId Hash
    , Array NodeId (SomeAST dom)
    )

instance NodeEqEnv dom (EqEnv dom)
  where
    prjNodeEqEnv   = snd
    modNodeEqEnv f = (id *** f)

instance VarEqEnv (EqEnv dom)
  where
    prjVarEqEnv   = fst
    modVarEqEnv f = (f *** id)

instance (AlphaEq dom dom dom env, NodeEqEnv dom env) =>
    AlphaEq (Node ctx) (Node ctx) dom env
  where
    alphaEqSym (Node n1) Nil (Node n2) Nil
        | n1 == n2  = return True
        | otherwise = do
            (hTab,nTab) :: NodeEnv dom <- asks prjNodeEqEnv
            if hTab!n1 /= hTab!n2
              then return False
              else case (nTab!n1, nTab!n2) of
                  (SomeAST a, SomeAST b) -> alphaEqM a b
                    -- TODO The result could be memoized in a
                    -- @Map (NodeId,NodeId) Bool@

  -- TODO With only this instance, the result will be 'False' when one argument
  --      is a 'Node' and the other one isn't. This is not really correct since
  --      'Node's are just meta-variables and shouldn't be part of the
  --      comparison. But as long as equivalent expressions always have 'Node's
  --      at the same position, it doesn't matter. This could probably be fixed
  --      by adding two overlapping instances.



-- | \"Abstract Syntax Graph\"
--
-- A representation of a syntax tree with explicit sharing. An 'ASG' is valid if
-- and only if 'inlineAll' succeeds (and the 'numNodes' field is correct).
data ASG ctx dom a = ASG
    { topExpression :: ASTF (Node ctx :+: dom) a               -- ^ Top-level expression
    , graphNodes    :: [(NodeId, SomeAST (Node ctx :+: dom))]  -- ^ Mapping from node id to sub-expression
    , numNodes      :: NodeId                                  -- ^ Total number of nodes
    }



-- | Show syntax graph using ASCII art
showASG :: ToTree dom => ASG ctx dom a -> String
showASG (ASG top nodes _) =
    unlines ((line "top" ++ showAST top) : map showNode nodes)
  where
    line str = "---- " ++ str ++ " " ++ rest ++ "\n"
      where
        rest = take (40 - length str) $ repeat '-'

    showNode (n, SomeAST expr) = concat
      [ line ("node:" ++ show n)
      , showAST expr
      ]

-- | Print syntax graph using ASCII art
drawASG :: ToTree dom => ASG ctx dom a -> IO ()
drawASG = putStrLn . showASG

-- | Update the node identifiers in an 'AST' using the supplied reindexing
-- function
reindexNodesAST ::
    (NodeId -> NodeId) -> AST (Node ctx :+: dom) a -> AST (Node ctx :+: dom) a
reindexNodesAST reix (Sym (InjL (Node n))) = Sym (InjL (Node $ reix n))
reindexNodesAST reix (f :$ a) = reindexNodesAST reix f :$ reindexNodesAST reix a
reindexNodesAST reix a = a

-- | Reindex the nodes according to the given index mapping. The number of nodes
-- is unchanged, so if the index mapping is not 1:1, the resulting graph will
-- contain duplicates.
reindexNodes :: (NodeId -> NodeId) -> ASG ctx dom a -> ASG ctx dom a
reindexNodes reix (ASG top nodes n) = ASG top' nodes' n
  where
    top'   = reindexNodesAST reix top
    nodes' =
      [ (reix n, SomeAST $ reindexNodesAST reix a)
        | (n, SomeAST a) <- nodes
      ]

-- | Reindex the nodes to be in the range @[0 .. l-1]@, where @l@ is the number
-- of nodes in the graph
reindexNodesFrom0 :: ASG ctx dom a -> ASG ctx dom a
reindexNodesFrom0 graph = reindexNodes reix graph
  where
    reix = reindex $ map fst $ graphNodes graph

-- | Remove duplicate nodes from a graph. The function only looks at the
-- 'NodeId' of each node. The 'numNodes' field is updated accordingly.
nubNodes :: ASG ctx dom a -> ASG ctx dom a
nubNodes (ASG top nodes n) = ASG top nodes' n'
  where
    nodes' = nubBy ((==) `on` fst) nodes
    n'     = genericLength nodes'

liftSome2
    :: (forall a b . ASTF (Node ctx :+: dom) a -> ASTF (Node ctx :+: dom) b -> c)
    -> SomeAST (Node ctx :+: dom)
    -> SomeAST (Node ctx :+: dom)
    -> c
liftSome2 f (SomeAST a) (SomeAST b) = f a b



--------------------------------------------------------------------------------
-- * Folding
--------------------------------------------------------------------------------

-- | Pattern functor representation of an 'AST' with 'Node's
data SyntaxPF dom a
  where
    AppPF  :: a -> a -> SyntaxPF dom a
    NodePF :: NodeId -> a -> SyntaxPF dom a
    DomPF  :: dom b -> SyntaxPF dom a
  -- NOTE: The important constructor is 'NodePF', which makes a 'Node' appear as
  -- any other recursive constructor.

instance Functor (SyntaxPF dom)
  where
    fmap f (AppPF g a)  = AppPF  (f g) (f a)
    fmap f (NodePF n a) = NodePF n (f a)
    fmap f (DomPF a)    = DomPF a



-- | Folding over a graph
--
-- The user provides a function to fold a single constructor (an \"algebra\").
-- The result contains the result of folding the whole graph as well as the
-- result of each internal node, represented both as an array and an association
-- list. Each node is processed exactly once.
foldGraph :: forall ctx dom a b
    .  (SyntaxPF dom b -> b)
    -> ASG ctx dom a
    -> (b, (Array NodeId b, [(NodeId,b)]))
foldGraph alg graph@(ASG top ns nn) = (g top, (arr,nodes))
  where
    nodes = [(n, g expr) | (n, SomeAST expr) <- ns]
    arr   = array (0, nn-1) nodes

    g :: Signature c => AST (Node ctx :+: dom) c -> b
    g (h :$ a)               = alg $ AppPF (g h) (g a)
    g (Sym (InjL (Node n)) ) = alg $ NodePF n (arr!n)
    g (Sym (InjR a))         = alg $ DomPF a



--------------------------------------------------------------------------------
-- * Inlining
--------------------------------------------------------------------------------

-- | Convert an 'ASG' to an 'AST' by inlining all nodes
inlineAll :: forall ctx dom a . Typeable a => ASG ctx dom a -> ASTF dom a
inlineAll (ASG top nodes n) = inline top
  where
    nodeMap = array (0, n-1) nodes

    inline :: forall b. (Typeable b, Signature b) =>
        AST (Node ctx :+: dom) b -> AST dom b
    inline (f :$ a) = inline f :$ inline a
    inline (Sym (InjL (Node n))) = case nodeMap ! n of
        SomeAST a -> case gcast a of
          Nothing -> error "inlineAll: type mismatch"
          Just a  -> inline a
    inline (Sym (InjR a)) = Sym a



-- | Find the child nodes of each node in an expression. The child nodes of a
-- node @n@ are the first nodes along all paths from @n@.
nodeChildren :: ASG ctx dom a -> [(NodeId, [NodeId])]
nodeChildren = map (id *** fromDList) . snd . snd . foldGraph children
  where
    children :: SyntaxPF dom (DList NodeId) -> DList (NodeId)
    children (AppPF ns1 ns2) = ns1 . ns2
    children (NodePF n _)    = single n
    children _               = empty

-- | Count the number of occurrences of each node in an expression
occurrences :: ASG ctx dom a -> Array NodeId Int
occurrences graph
    = count (0, numNodes graph - 1)
    $ concatMap snd
    $ nodeChildren graph

-- | Inline all nodes that are not shared
inlineSingle :: forall ctx dom a . Typeable a => ASG ctx dom a -> ASG ctx dom a
inlineSingle graph@(ASG top nodes n) = ASG top' nodes' n'
  where
    nodeTab  = array (0, n-1) nodes
    occs     = occurrences graph

    top'   = inline top
    nodes' = [(n, SomeAST (inline a)) | (n, SomeAST a) <- nodes, occs!n > 1]
    n'     = genericLength nodes'

    inline :: forall b. (Typeable b, Signature b) =>
        AST (Node ctx :+: dom) b -> AST (Node ctx :+: dom) b
    inline (f :$ a) = inline f :$ inline a
    inline (Sym (InjL (Node n)))
        | occs!n > 1 = Sym (InjL (Node n))
        | otherwise = case nodeTab ! n of
            SomeAST a -> case gcast a of
                Nothing -> error "inlineSingle: type mismatch"
                Just a  -> inline a
    inline (Sym (InjR a)) = Sym (InjR a)



--------------------------------------------------------------------------------
-- * Sharing
--------------------------------------------------------------------------------

-- | Compute a table (both array and list representation) of hash values for
-- each node
hashNodes :: ExprEq dom =>
    ASG ctx dom a -> (Array NodeId Hash, [(NodeId, Hash)])
hashNodes = snd . foldGraph hashNode
  where
    hashNode (AppPF h1 h2) = hashInt 0 `combine` h1 `combine` h2
    hashNode (NodePF _ h)  = h
    hashNode (DomPF a)     = hashInt 1 `combine` exprHash a



-- | Partitions the nodes such that two nodes are in the same sub-list if and
-- only if they are alpha-equivalent.
partitionNodes :: forall ctx dom a
    .  ( ExprEq dom
       , AlphaEq dom dom (Node ctx :+: dom) (EqEnv (Node ctx :+: dom))
       )
    => ASG ctx dom a -> [[NodeId]]
partitionNodes graph = concatMap (fullPartition nodeEq) approxPartitioning
  where
    nTab          = array (0, numNodes graph - 1) (graphNodes graph)
    (hTab,hashes) = hashNodes graph

    -- | An approximate partitioning of the nodes: nodes in different partitions
    -- are guaranteed to be inequivalent, while nodes in the same partition
    -- might be equivalent.
    approxPartitioning
        = map (map fst)
        $ groupBy ((==) `on` snd)
        $ sortBy (compare `on` snd)
        $ hashes

    nodeEq :: NodeId -> NodeId -> Bool
    nodeEq n1 n2 = runReader
        (liftSome2 alphaEqM (nTab!n1) (nTab!n2))
        (([],(hTab,nTab)) :: EqEnv (Node ctx :+: dom))



-- | Common sub-expression elimination based on alpha-equivalence
cse
    :: ( ExprEq dom
       , AlphaEq dom dom (Node ctx :+: dom) (EqEnv (Node ctx :+: dom))
       )
    => ASG ctx dom a -> ASG ctx dom a
cse graph@(ASG top nodes n) = nubNodes $ reindexNodes (reixTab!) graph
  where
    parts   = partitionNodes graph
    reixTab = array (0,n-1) [(n,p) | (part,p) <- parts `zip` [0..], n <- part]

