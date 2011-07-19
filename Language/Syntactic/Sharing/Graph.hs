-- | A representation of abstract syntax graphs

module Language.Syntactic.Sharing.Graph where



import Data.Array
import Data.Typeable

import Language.Syntactic



-- | Node identifier
newtype NodeId = NodeId { nodeInteger :: Integer }
  deriving (Eq, Ord, Num, Enum, Ix)



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

instance ExprEq (Node ctx)
  where
    Node n1 `exprEq` Node n2 = n1==n2

instance Render (Node ctx)
  where
    render (Node a) = showNode a

instance ToTree (Node ctx)



-- | An 'ASTF' with hidden result type
data SomeAST dom
  where
    SomeAST :: Typeable a => ASTF dom a -> SomeAST dom



-- | \"Abstract Syntax Graph\"
--
-- A representation of a syntax tree with explicit
-- node sharing. It is assumed that nodes are enumerated from 0, so 'numNodes'
-- returns the number of identifiers as well as the next available identifier.
--
-- An 'ASG' is valid if and only if 'inline' succeeds (and the 'numNodes' field
-- is correct).
data ASG ctx dom a = ASG
    { topExpression :: ASTF (Node ctx :+: dom) a               -- ^ Top-level expression
    , graphNodes    :: [(NodeId, SomeAST (Node ctx :+: dom))]  -- ^ Mapping from node id to sub-expression
    , numNodes      :: NodeId                                  -- ^ Total number of nodes
    }



-- | Convert an 'ASG' to an 'AST' by inlining all nodes
inline :: forall ctx dom a . Typeable a => ASG ctx dom a -> ASTF dom a
inline graph@(ASG {}) = rebuild (topExpression graph)
  where
    nodeMap = array (0, numNodes graph - 1) (graphNodes graph)

    rebuild :: forall b. (Typeable b, ConsType b) =>
        AST (Node ctx :+: dom) b -> AST dom b
    rebuild (f :$: a)                   = rebuild f :$: rebuild a
    rebuild (Symbol (InjectL (Node n))) = case nodeMap ! n of
        SomeAST a -> case gcast a of
          Nothing -> error "inline: type mismatch"
          Just a  -> rebuild a
    rebuild (Symbol (InjectR a)) = Symbol a



-- | Pattern functor representation of an 'AST' with 'Node's
data SyntaxPF dom a
  where
    AppPF  :: a -> a -> SyntaxPF dom a
    NodePF :: NodeId -> a -> SyntaxPF dom a
    DomPF  :: dom b -> SyntaxPF dom a
  -- NOTE: The important constructor is 'NodePF', which makes a 'Noe' appear as
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

    g :: ConsType c => AST (Node ctx :+: dom) c -> b
    g (h :$: a)                    = alg $ AppPF (g h) (g a)
    g (Symbol (InjectL (Node n)) ) = alg $ NodePF n (arr!n)
    g (Symbol (InjectR a))         = alg $ DomPF a



-- | Show syntax graph using ASCII art
showASG :: ToTree dom => ASG ctx dom a -> String
showASG (ASG {topExpression = top, graphNodes = nodes}) =
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

