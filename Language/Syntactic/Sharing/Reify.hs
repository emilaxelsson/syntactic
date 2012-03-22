-- | Reifying the sharing in an 'AST'
--
-- This module is based on /Type-Safe Observable Sharing in Haskell/ (Andy Gill,
-- /Haskell Symposium/, 2009).

module Language.Syntactic.Sharing.Reify
    ( reifyGraph
    ) where



import Control.Monad.Writer
import Data.IntMap as Map
import Data.IORef
import Data.Typeable
import System.Mem.StableName

import Language.Syntactic
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.StableName



-- | Shorthand used by 'reifyGraphM'
--
-- Writes out a list of encountered nodes and returns the top expression.
type GraphMonad ctx dom a = WriterT
      [(NodeId, SomeAST (Node ctx :+: dom))]
      IO
      (AST (Node ctx :+: dom) a)



reifyGraphM :: forall ctx dom a . Typeable a
    => (forall a . ASTF dom a -> Maybe (SatWit ctx a))
    -> IORef NodeId
    -> IORef (History (AST dom))
    -> ASTF dom a
    -> GraphMonad ctx dom (Full a)

reifyGraphM canShare nSupp history = reifyNode
  where
    reifyNode :: Typeable b => ASTF dom b -> GraphMonad ctx dom (Full b)
    reifyNode a = case canShare a of
        Nothing -> reifyRec a
        Just SatWit | a `seq` True -> do
          st   <- liftIO $ makeStableName a
          hist <- liftIO $ readIORef history
          case lookHistory hist (StName st) of
            Just n -> return $ Sym $ InjL $ Node n
            _ -> do
              n  <- fresh nSupp
              liftIO $ modifyIORef history $ remember (StName st) n
              a' <- reifyRec a
              tell [(n, SomeAST a')]
              return $ Sym $ InjL $ Node n

    reifyRec :: AST dom b -> GraphMonad ctx dom b
    reifyRec (f :$ a) = liftM2 (:$) (reifyRec f) (reifyNode a)
    reifyRec (Sym a)  = return $ Sym (InjR a)



-- | Convert a syntax tree to a sharing-preserving graph
--
-- This function is not referentially transparent (hence the 'IO'). However, it
-- is well-behaved in the sense that the worst thing that could happen is that
-- sharing is lost. It is not possible to get false sharing.
reifyGraph :: Typeable a
    => (forall a . ASTF dom a -> Maybe (SatWit ctx a))
         -- ^ A function that decides whether a given node can be shared.
         -- 'Nothing' means \"don't share\"; 'Just' means \"share\". Nodes whose
         -- result type fulfills @(`Sat` ctx a)@ can be shared, which is why the
         -- function returns a 'SatWit'.
    -> ASTF dom a
    -> IO (ASG ctx dom a)
reifyGraph canShare a = do
    nSupp   <- newIORef 0
    history <- newIORef empty
    (a',ns) <- runWriterT $ reifyGraphM canShare nSupp history a
    n       <- readIORef nSupp
    return (ASG a' ns n)

