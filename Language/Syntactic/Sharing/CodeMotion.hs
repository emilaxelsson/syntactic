module Language.Syntactic.Sharing.CodeMotion where



import Control.Arrow
import Data.Array
import Data.Function
import Data.List
import Data.Typeable

import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Binding.Types



--------------------------------------------------------------------------------
-- * Code motion
--------------------------------------------------------------------------------

-- | Computes an ordering between the bound variables in an expression. If the
-- variable @v1@ appears later than @v2@ in the list, then the expression
-- binding @v2@ cannot be local to the expression binding @v1@.
bindOrder :: LambdaForest expr a -> [VarId]
bindOrder = fromDList . fst . foldForest order
  where
    order (LamFold v vs)    = single v . vs
    order (AppFold vs1 vs2) = vs1 . vs2
    order (NodeFold _ vs)   = vs
    order _                 = empty

-- | Compute a comparison function for variables in an expression. If, according
-- to this function, @v1 > v2@, then the expression binding @v2@ cannot be local
-- to the expression binding @v1@.
bindCompare :: LambdaForest expr a -> (VarId -> VarId -> Ordering)
bindCompare forest = compare `on` (arr!)
  where
    arr = array (0, numVars forest - 1) $ zip (bindOrder forest) [0..]

-- | Computes the set of free variables for each node in an expression
freeVars :: LambdaForest expr a -> [(NodeId, [VarId])]
freeVars = snd . snd . foldForest deps
  where
    deps (VarFold v)       = [v]
    deps (LamFold v vs)    = delete v vs
    deps (AppFold vs1 vs2) = vs1 ++ vs2
    deps (NodeFold _ vs)   = vs
    deps _                 = []

nodeParent :: LambdaForest expr a -> [(NodeId, NodeId)]
nodeParent forest = [(nChild,n) | (n,ns) <- nodeChildren forest, nChild <- ns]



-- | Rebuild a 'LambdaForest' as a 'Lambda' expression. Nodes are eliminated,
-- either by inlining or let-lifting.
rebuildWithLet :: forall expr a
    .  Typeable a
    => (NodeId -> Bool)     -- ^ Which nodes should be let-lifted
    -> (VarId -> [NodeId])  -- ^ Which nodes should be moved to the given binding
    -> LambdaForest expr a
    -> Lambda expr a
rebuildWithLet shouldLift toBeMoved forest =
    rebuild (topExpression forest)
  where
    nodeMap     = array (0, numNodes forest - 1) (forestNodes forest)
    nodeToVar n = numVars forest + fromInteger (nodeInteger n)

    mkLet :: Typeable b =>
        (VarId, SomeLambda (Node expr)) -> Lambda expr b -> Lambda expr b
    mkLet (v, SomeLambda a) b = Let :$: rebuild a :$: Lambda v b

    rebuild :: Typeable b => LambdaNode expr b -> Lambda expr b
    rebuild (Variable v) = Variable v
    rebuild (Lambda v a) = Lambda v $ foldr mkLet (rebuild a)
      [(nodeToVar n, nodeMap ! n) | n <- toBeMoved v, shouldLift n]
    rebuild (f :$: a) = rebuild f :$: rebuild a
    rebuild Let       = Let
    rebuild (Inject (NodeExpr a)) = Inject a
    rebuild (Inject (Node n))
      | shouldLift n = Variable (nodeToVar n)
      | otherwise    = case nodeMap ! n of
          SomeLambda a -> case gcast a of
            Nothing -> error "rebuildWithLet: type mismatch"
            Just a  -> rebuild a

