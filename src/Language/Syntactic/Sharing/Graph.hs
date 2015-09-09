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

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Sharing.Utils



--------------------------------------------------------------------------------
-- * Representation
--------------------------------------------------------------------------------

-- | Node identifier
newtype NodeId = NodeId { nodeInteger :: Integer }
  deriving (Eq, Ord, Num, Real, Integral, Enum, Ix)

instance Show NodeId
  where
    show (NodeId i) = show i

showNode :: NodeId -> String
showNode n = "node:" ++ show n



-- | Placeholder for a syntax tree
data Node a
  where
    Node :: NodeId -> Node (Full a)

instance Constrained Node
  where
    {-# SPECIALIZE instance Constrained Node #-}
    {-# INLINABLE exprDict #-}
    type Sat Node = Top
    exprDict _ = Dict

instance Render Node
  where
    {-# INLINABLE renderSym #-}
    renderSym (Node a) = showNode a

instance StringTree Node



-- | Environment for alpha-equivalence
class NodeEqEnv dom a
  where
    prjNodeEqEnv :: a -> NodeEnv dom (Sat dom)
    modNodeEqEnv :: (NodeEnv dom (Sat dom) -> NodeEnv dom (Sat dom)) -> (a -> a)

type EqEnv dom p = ([(VarId,VarId)], NodeEnv dom p)

type NodeEnv dom p =
    ( Array NodeId Hash
    , Array NodeId (ASTB dom p)
    )

instance (p ~ Sat dom) => NodeEqEnv dom (EqEnv dom p)
  where
    {-# SPECIALIZE instance (p ~ Sat dom) => NodeEqEnv dom (EqEnv dom p) #-}
    {-# INLINABLE prjNodeEqEnv #-}
    {-# INLINABLE modNodeEqEnv #-}
    prjNodeEqEnv   = snd
    modNodeEqEnv f = (id *** f)

instance VarEqEnv (EqEnv dom p)
  where
    {-# SPECIALIZE instance VarEqEnv (EqEnv dom p) #-}
    {-# INLINABLE prjVarEqEnv #-}
    {-# INLINABLE modVarEqEnv #-}
    prjVarEqEnv   = fst
    modVarEqEnv f = (f *** id)

instance (AlphaEq dom dom dom env, NodeEqEnv dom env) =>
    AlphaEq Node Node dom env
  where
    {-# SPECIALIZE instance (AlphaEq dom dom dom env, NodeEqEnv dom env) =>
          AlphaEq Node Node dom env #-}
    {-# INLINABLE alphaEqSym #-}
    alphaEqSym (Node n1) Nil (Node n2) Nil
        | n1 == n2  = return True
        | otherwise = do
            (hTab,nTab) :: NodeEnv dom (Sat dom) <- asks prjNodeEqEnv
            if hTab!n1 /= hTab!n2
              then return False
              else case (nTab!n1, nTab!n2) of
                  (ASTB a, ASTB b) -> alphaEqM a b
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
data ASG dom a = ASG
    { topExpression :: ASTF (NodeDomain dom) a              -- ^ Top-level expression
    , graphNodes    :: [(NodeId, ASTSAT (NodeDomain dom))]  -- ^ Mapping from node id to sub-expression
    , numNodes      :: NodeId                               -- ^ Total number of nodes
    }

type NodeDomain dom = (Node :+: dom) :|| Sat dom



-- | Show syntax graph using ASCII art
showASG :: forall dom a. StringTree dom => ASG dom a -> String
showASG (ASG top nodes _) =
    unlines ((line "top" ++ showAST top) : map showNode nodes)
  where
    line str = "---- " ++ str ++ " " ++ rest ++ "\n"
      where
        rest = replicate (40 - length str) '-'

    showNode :: (NodeId, ASTSAT (NodeDomain dom)) -> String
    showNode (n, ASTB expr) = concat
      [ line ("node:" ++ show n)
      , showAST expr
      ]

-- | Print syntax graph using ASCII art
drawASG :: StringTree dom => ASG dom a -> IO ()
drawASG = putStrLn . showASG

-- | Update the node identifiers in an 'AST' using the supplied reindexing
-- function
reindexNodesAST ::
    (NodeId -> NodeId) -> AST (NodeDomain dom) a -> AST (NodeDomain dom) a
reindexNodesAST reix (Sym (C' (InjL (Node n)))) = injC $ Node $ reix n
reindexNodesAST reix (s :$ a) = reindexNodesAST reix s :$ reindexNodesAST reix a
reindexNodesAST reix a = a

-- | Reindex the nodes according to the given index mapping. The number of nodes
-- is unchanged, so if the index mapping is not 1:1, the resulting graph will
-- contain duplicates.
reindexNodes :: (NodeId -> NodeId) -> ASG dom a -> ASG dom a
reindexNodes reix (ASG top nodes n) = ASG top' nodes' n
  where
    top'   = reindexNodesAST reix top
    nodes' =
      [ (reix n, ASTB $ reindexNodesAST reix a)
        | (n, ASTB a) <- nodes
      ]

-- | Reindex the nodes to be in the range @[0 .. l-1]@, where @l@ is the number
-- of nodes in the graph
reindexNodesFrom0 :: ASG dom a -> ASG dom a
reindexNodesFrom0 graph = reindexNodes reix graph
  where
    reix = reindex $ map fst $ graphNodes graph

-- | Remove duplicate nodes from a graph. The function only looks at the
-- 'NodeId' of each node. The 'numNodes' field is updated accordingly.
nubNodes :: ASG dom a -> ASG dom a
nubNodes (ASG top nodes n) = ASG top nodes' n'
  where
    nodes' = nubBy ((==) `on` fst) nodes
    n'     = genericLength nodes'



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
foldGraph :: forall dom a b .
    (SyntaxPF dom b -> b) -> ASG dom a -> (b, (Array NodeId b, [(NodeId,b)]))
foldGraph alg (ASG top ns nn) = (g top, (arr,nodes))
  where
    nodes = [(n, g expr) | (n, ASTB expr) <- ns]
    arr   = array (0, nn-1) nodes

    g :: AST (NodeDomain dom) c -> b
    g (h :$ a)                   = alg $ AppPF (g h) (g a)
    g (Sym (C' (InjL (Node n)))) = alg $ NodePF n (arr!n)
    g (Sym (C' (InjR a)))        = alg $ DomPF a



--------------------------------------------------------------------------------
-- * Inlining
--------------------------------------------------------------------------------

-- | Convert an 'ASG' to an 'AST' by inlining all nodes
inlineAll :: forall dom a . ConstrainedBy dom Typeable =>
    ASG dom a -> ASTF dom a
inlineAll (ASG top nodes n) = inline top
  where
    nodeMap = array (0, n-1) nodes

    inline :: AST (NodeDomain dom) b -> AST dom b
    inline (s :$ a) = inline s :$ inline a
    inline s@(Sym (C' (InjL (Node n)))) = case nodeMap ! n of
        ASTB a
          | Dict <- exprDictSub pTypeable s
          , Dict <- exprDictSub pTypeable a
          -> case gcast a of
               Nothing -> error "inlineAll: type mismatch"
               Just a  -> inline a
    inline (Sym (C' (InjR a))) = Sym a



-- | Find the child nodes of each node in an expression. The child nodes of a
-- node @n@ are the first nodes along all paths from @n@.
nodeChildren :: ASG dom a -> [(NodeId, [NodeId])]
nodeChildren = map (id *** fromDList) . snd . snd . foldGraph children
  where
    children :: SyntaxPF dom (DList NodeId) -> DList NodeId
    children (AppPF ns1 ns2) = ns1 . ns2
    children (NodePF n _)    = single n
    children _               = empty

-- | Count the number of occurrences of each node in an expression
occurrences :: ASG dom a -> Array NodeId Int
occurrences graph
    = count (0, numNodes graph - 1)
    $ concatMap snd
    $ nodeChildren graph

-- | Inline all nodes that are not shared
inlineSingle :: forall dom a . ConstrainedBy dom Typeable =>
    ASG dom a -> ASG dom a
inlineSingle graph@(ASG top nodes n) = ASG top' nodes' n'
  where
    nodeTab  = array (0, n-1) nodes
    occs     = occurrences graph

    top'   = inline top
    nodes' = [(n, ASTB (inline a)) | (n, ASTB a) <- nodes, occs!n > 1]
    n'     = genericLength nodes'

    inline :: AST (NodeDomain dom) b -> AST (NodeDomain dom) b
    inline (s :$ a) = inline s :$ inline a
    inline s@(Sym (C' (InjL (Node n))))
        | occs!n > 1 = injC $ Node n
        | otherwise = case nodeTab ! n of
            ASTB a
              | Dict <- exprDictSub pTypeable s
              , Dict <- exprDictSub pTypeable a
              -> case gcast a of
                   Nothing -> error "inlineSingle: type mismatch"
                   Just a  -> inline a
    inline (Sym (C' (InjR a))) = Sym $ C' $ InjR a



--------------------------------------------------------------------------------
-- * Sharing
--------------------------------------------------------------------------------

-- | Compute a table (both array and list representation) of hash values for
-- each node
hashNodes :: Equality dom => ASG dom a -> (Array NodeId Hash, [(NodeId, Hash)])
hashNodes = snd . foldGraph hashNode
  where
    hashNode (AppPF h1 h2) = hashInt 0 `combine` h1 `combine` h2
    hashNode (NodePF _ h)  = h
    hashNode (DomPF a)     = hashInt 1 `combine` exprHash a



-- | Partitions the nodes such that two nodes are in the same sub-list if and
-- only if they are alpha-equivalent.
partitionNodes :: forall dom a
    .  ( Equality dom
       , AlphaEq dom dom (NodeDomain dom) (EqEnv (NodeDomain dom) (Sat dom))
       )
    => ASG dom a -> [[NodeId]]
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
        (liftASTB2 alphaEqM (nTab!n1) (nTab!n2))
        (([],(hTab,nTab)) :: EqEnv (NodeDomain dom) (Sat dom))



-- | Common sub-expression elimination based on alpha-equivalence
cse
    :: ( Equality dom
       , AlphaEq dom dom (NodeDomain dom) (EqEnv (NodeDomain dom) (Sat dom))
       )
    => ASG dom a -> ASG dom a
cse graph@(ASG top nodes n) = nubNodes $ reindexNodes (reixTab!) graph
  where
    parts   = partitionNodes graph
    reixTab = array (0,n-1) [(n,p) | (part,p) <- parts `zip` [0..], n <- part]
