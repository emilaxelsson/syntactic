-- | This module is similar to "Language.Syntactic.Sharing.Reify", but operates
-- on @`AST` (`HODomain` ctx dom)@ rather than a general 'AST'. The reason for
-- having this module is that when using 'HODomain', it is important to do
-- simultaneous sharing analysis and 'HOLambda' reification. Obviously we cannot
-- do sharing analysis first (using
-- 'Language.Syntactic.Sharing.Reify.reifyGraph' from
-- "Language.Syntactic.Sharing.Reify"), since it needs to be able to look inside
-- 'HOLambda'. On the other hand, if we did 'HOLambda' reification first (using
-- 'reify'), we would destroy the sharing.
--
-- This module is based on /Type-Safe Observable Sharing in Haskell/ (Andy Gill,
-- /Haskell Symposium/, 2009).

module Language.Syntactic.Sharing.ReifyHO
    ( reifyGraphTop
    , reifyGraph
    ) where



import Control.Monad.Writer
import Data.IntMap as Map
import Data.IORef
import Data.Typeable
import System.Mem.StableName

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.StableName
import qualified Language.Syntactic.Sharing.Reify  -- For Haddock



-- | Shorthand used by 'reifyGraphM'
--
-- Writes out a list of encountered nodes and returns the top expression.
type GraphMonad ctx dom a = WriterT
      [(NodeId, SomeAST (Node ctx :+: Lambda ctx :+: Variable ctx :+: dom))]
      IO
      (AST (Node ctx :+: Lambda ctx :+: Variable ctx :+: dom) a)



reifyGraphM :: forall ctx dom a . Typeable a
    => (forall a . ASTF (HODomain ctx dom) a -> Maybe (SatWit ctx a))
    -> IORef VarId
    -> IORef NodeId
    -> IORef (History (AST (HODomain ctx dom)))
    -> ASTF (HODomain ctx dom) a
    -> GraphMonad ctx dom (Full a)

reifyGraphM canShare vSupp nSupp history = reifyNode
  where
    reifyNode :: Typeable b =>
        ASTF (HODomain ctx dom) b -> GraphMonad ctx dom (Full b)
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

    reifyRec :: AST (HODomain ctx dom) b -> GraphMonad ctx dom b
    reifyRec (f :$ a)       = liftM2 (:$) (reifyRec f) (reifyNode a)
    reifyRec (Sym (InjR a)) = return $ Sym (InjR (InjR a))
    reifyRec (Sym (InjL (HOLambda f))) = do
        v    <- fresh vSupp
        body <- reifyNode $ f $ inj $ (Variable v `withContext` ctx)
        return $ inj (Lambda v `withContext` ctx) :$ body
      where
        ctx = Proxy :: Proxy ctx



-- | Convert a syntax tree to a sharing-preserving graph
reifyGraphTop :: Typeable a
    => (forall a . ASTF (HODomain ctx dom) a -> Maybe (SatWit ctx a))
    -> ASTF (HODomain ctx dom) a
    -> IO (ASG ctx (Lambda ctx :+: Variable ctx :+: dom) a, VarId)
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
reifyGraph :: Syntactic a (HODomain ctx dom)
    => (forall a . ASTF (HODomain ctx dom) a -> Maybe (SatWit ctx a))
         -- ^ A function that decides whether a given node can be shared.
         -- 'Nothing' means \"don't share\"; 'Just' means \"share\". Nodes whose
         -- result type fulfills @(`Sat` ctx a)@ can be shared, which is why the
         -- function returns a 'SatWit'.
    -> a
    -> IO
        ( ASG ctx (Lambda ctx :+: Variable ctx :+: dom) (Internal a)
        , VarId
        )
reifyGraph canShare = reifyGraphTop canShare . desugar

