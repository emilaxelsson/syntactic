-- | Reifying the sharing in an 'AST'
--
-- This module is based on the paper /Type-Safe Observable Sharing in Haskell/
-- (Andy Gill, 2009, <http://dx.doi.org/10.1145/1596638.1596653>).

module Language.Syntactic.Sharing.Reify
    ( reifyGraph
    ) where



import Control.Monad.Writer
import Data.IntMap as Map
import Data.IORef
import System.Mem.StableName

import Language.Syntactic
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.StableName



-- | Shorthand used by 'reifyGraphM'
--
-- Writes out a list of encountered nodes and returns the top expression.
type GraphMonad dom a = WriterT
      [(NodeId, ASTB (NodeDomain dom))]
      IO
      (AST (NodeDomain dom) a)



reifyGraphM :: forall dom a . Constrained dom
    => (forall a . ASTF dom a -> Bool)
    -> IORef NodeId
    -> IORef (History (AST dom))
    -> ASTF dom a
    -> GraphMonad dom (Full a)

reifyGraphM canShare nSupp history = reifyNode
  where
    reifyNode :: ASTF dom b -> GraphMonad dom (Full b)
    reifyNode a
      | Dict <- exprDict a = case canShare a of
          False               -> reifyRec a
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

    reifyRec :: Sat dom (DenResult b) => AST dom b -> GraphMonad dom b
    reifyRec (f :$ a) = liftM2 (:$) (reifyRec f) (reifyNode a)
    reifyRec (Sym s)  = return $ Sym $ C' $ InjR s



-- | Convert a syntax tree to a sharing-preserving graph
--
-- This function is not referentially transparent (hence the 'IO'). However, it
-- is well-behaved in the sense that the worst thing that could happen is that
-- sharing is lost. It is not possible to get false sharing.
reifyGraph :: Constrained dom
    => (forall a . ASTF dom a -> Bool)
         -- ^ A function that decides whether a given node can be shared
    -> ASTF dom a
    -> IO (ASG dom a)
reifyGraph canShare a = do
    nSupp   <- newIORef 0
    history <- newIORef empty
    (a',ns) <- runWriterT $ reifyGraphM canShare nSupp history a
    n       <- readIORef nSupp
    return (ASG a' ns n)

