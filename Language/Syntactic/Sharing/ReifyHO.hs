-- | This module is similar to "Language.Syntactic.Sharing.Reify", but operates
-- on @`AST` (`HODomain` dom p)@ rather than a general 'AST'. The reason for
-- having this module is that when using 'HODomain', it is important to do
-- simultaneous sharing analysis and 'HOLambda' reification. Obviously we cannot
-- do sharing analysis first (using
-- 'Language.Syntactic.Sharing.Reify.reifyGraph' from
-- "Language.Syntactic.Sharing.Reify"), since it needs to be able to look inside
-- 'HOLambda'. On the other hand, if we did 'HOLambda' reification first (using
-- 'reify'), we would destroy the sharing.
--
-- This module is based on the paper /Type-Safe Observable Sharing in Haskell/
-- (Andy Gill, 2009, <http://dx.doi.org/10.1145/1596638.1596653>).

module Language.Syntactic.Sharing.ReifyHO
    ( reifyGraphTop
    , reifyGraph
    ) where



import Control.Monad.Writer
import Data.IntMap as Map
import Data.IORef
import System.Mem.StableName

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.StableName
import qualified Language.Syntactic.Sharing.Reify  -- For Haddock



-- | Shorthand used by 'reifyGraphM'
--
-- Writes out a list of encountered nodes and returns the top expression.
type GraphMonad dom p pVar a = WriterT
    [(NodeId, ASTB (NodeDomain (FODomain dom p pVar)) p)]
    IO
    (AST (NodeDomain (FODomain dom p pVar)) a)



reifyGraphM :: forall dom p pVar a
    .  (forall a . ASTF (HODomain dom p pVar) a -> Bool)
    -> IORef VarId
    -> IORef NodeId
    -> IORef (History (AST (HODomain dom p pVar)))
    -> ASTF (HODomain dom p pVar) a
    -> GraphMonad dom p pVar (Full a)

reifyGraphM canShare vSupp nSupp history = reifyNode
  where
    reifyNode :: ASTF (HODomain dom p pVar) b -> GraphMonad dom p pVar (Full b)
    reifyNode a
      | Dict <- exprDict a = case canShare a of
          False -> reifyRec a
          True | a `seq` True -> do
            st   <- liftIO $ makeStableName a
            hist <- liftIO $ readIORef history
            case lookHistory hist (StName st) of
              Just n -> return $ injC $ Node n
              _ -> do
                n  <- fresh nSupp
                liftIO $ modifyIORef history $ remember (StName st) n
                a' <- reifyRec a
                tell [(n, ASTB a')]
                return $ injC $ Node n

    reifyRec :: AST (HODomain dom p pVar) b -> GraphMonad dom p pVar b
    reifyRec (f :$ a)            = liftM2 (:$) (reifyRec f) (reifyNode a)
    reifyRec (Sym (C' (InjR a))) = return $ Sym $ C' $ InjR $ C' $ InjR a
    reifyRec (Sym (C' (InjL (HOLambda f)))) = do
        v    <- fresh vSupp
        body <- reifyNode $ f $ injC $ symType pVar $ C' (Variable v)
        return $ injC (symType pLam $ SubConstr2 (Lambda v)) :$ body
      where
        pVar = P::P (Variable :|| pVar)
        pLam = P::P (SubConstr2 Lambda pVar Top)



-- | Convert a syntax tree to a sharing-preserving graph
reifyGraphTop
    :: (forall a . ASTF (HODomain dom p pVar) a -> Bool)
    -> ASTF (HODomain dom p pVar) a
    -> IO (ASG (FODomain dom p pVar) a, VarId)
reifyGraphTop canShare a = do
    vSupp   <- newIORef 0
    nSupp   <- newIORef 0
    history <- newIORef empty
    (a',ns) <- runWriterT $ reifyGraphM canShare vSupp nSupp history a
    v       <- readIORef vSupp
    n       <- readIORef nSupp
    return (ASG a' ns n, v)

-- | Reifying an n-ary syntactic function to a sharing-preserving graph
--
-- This function is not referentially transparent (hence the 'IO'). However, it
-- is well-behaved in the sense that the worst thing that could happen is that
-- sharing is lost. It is not possible to get false sharing.
reifyGraph :: Syntactic a (HODomain dom p pVar)
    => (forall a . ASTF (HODomain dom p pVar) a -> Bool)
         -- ^ A function that decides whether a given node can be shared
    -> a
    -> IO (ASG (FODomain dom p pVar) (Internal a), VarId)
reifyGraph canShare = reifyGraphTop canShare . desugar

