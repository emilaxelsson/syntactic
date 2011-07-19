module Language.Syntactic.Sharing.Reify where



import Control.Monad.Writer
import Data.IntMap as Map
import Data.IORef
import Data.Typeable
import System.Mem.StableName
import Unsafe.Coerce

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Sharing.Graph



-- | 'StableName' of a 'HOASTF' with hidden result type
data StName ctx dom
  where
    StName :: Typeable a => StableName (HOASTF ctx dom a) -> StName ctx dom

stCast :: forall a b ctx dom . (Typeable a, Typeable b) =>
    StableName (HOASTF ctx dom a) -> Maybe (StableName (HOASTF ctx dom b))
stCast a
    | ta==tb    = Just (unsafeCoerce a)
    | otherwise = Nothing
  where
    ta = typeOf (undefined :: a)
    tb = typeOf (undefined :: b)

instance Eq (StName ctx dom)
  where
    StName st1 == StName st2 = case stCast st1 of
        Just st1' -> st1'==st2
        _         -> False

hash :: StName ctx dom -> Int
hash (StName st) = hashStableName st



-- 'History' implements a hash table from 'StName' to 'NodeId' (with 'hash' as
-- the hashing function). I.e. it is assumed that the 'StName's at each entry
-- all have the same 'hash', and that this number is equal to the entry's key.
type History ctx dom = IntMap [(StName ctx dom, NodeId)]

lookHistory :: History ctx dom -> StName ctx dom -> Maybe NodeId
lookHistory hist st = case Map.lookup (hash st) hist of
    Nothing   -> Nothing
    Just list -> Prelude.lookup st list

remember :: StName ctx dom -> NodeId -> History ctx dom -> History ctx dom
remember st n hist = insertWith (++) (hash st) [(st,n)] hist

-- | Return a fresh identifier from the given supply
fresh :: (Num a, MonadIO m) => IORef a -> m a
fresh aRef = do
    a <- liftIO $ readIORef aRef
    liftIO $ writeIORef aRef (a+1)
    return a



-- | Shorthand used by 'reifyGraphM'
--
-- Writes out a list of encountered nodes and returns the top expression.
type GraphMonad ctx dom a = WriterT
      [(NodeId, SomeAST (Node ctx :+: Lambda ctx :+: Variable ctx :+: dom))]
      IO
      (AST (Node ctx :+: Lambda ctx :+: Variable ctx :+: dom) a)



reifyGraphM :: forall ctx dom a . Typeable a
    => (forall a . HOASTF ctx dom a -> Maybe (Witness' ctx a))
    -> IORef VarId
    -> IORef NodeId
    -> IORef (History ctx dom)
    -> HOASTF ctx dom a
    -> GraphMonad ctx dom (Full a)

reifyGraphM canShare vSupp nSupp history = reifyNode
  where
    reifyNode :: Typeable b => HOASTF ctx dom b -> GraphMonad ctx dom (Full b)
    reifyNode a = case canShare a of
        Nothing       -> reifyRec a
        Just Witness' -> do
          st   <- liftIO $ makeStableName a
          hist <- liftIO $ readIORef history
          case lookHistory hist (StName st) of
            Just n -> error "sdfsdf" -- return $ Symbol $ InjectL $ Node n
            _ -> do
              n  <- fresh nSupp
              liftIO $ modifyIORef history $ remember (StName st) n
              a' <- reifyRec a
              tell [(n, SomeAST a')]
              return $ Symbol $ InjectL $ Node n

    reifyRec :: HOAST ctx dom b -> GraphMonad ctx dom b
    reifyRec (f :$: a)            = liftM2 (:$:) (reifyRec f) (reifyNode a)
    reifyRec (Symbol (InjectR a)) = return $ Symbol (InjectR (InjectR a))
    reifyRec (Symbol (InjectL (HOLambda f))) = do
        v    <- fresh vSupp
        body <- reifyNode $ f $ inject $ (Variable v `withContext` ctx)
        return $ inject (Lambda v `withContext` ctx) :$: body
      where
        ctx = Proxy :: Proxy ctx



-- | Convert a 'HOASTF' expression into an 'ASG'. The resulting graph reifies
-- the sharing in the given expression.
reifyGraphHOAST :: Typeable a
    => (forall a . HOASTF ctx dom a -> Maybe (Witness' ctx a))
    -> HOASTF ctx dom a
    -> IO (ASG ctx (Lambda ctx :+: Variable ctx :+: dom) a, VarId)

reifyGraphHOAST canShare a = do
    vSupp   <- newIORef 0
    nSupp   <- newIORef 0
    history <- newIORef empty
    (a',ns) <- runWriterT $ reifyGraphM canShare vSupp nSupp history a
    v       <- readIORef vSupp
    n       <- readIORef nSupp
    return (ASG a' ns n, v)
  -- It is important to do simultaneous sharing analysis and 'HOLambda'
  -- reification. Obviously we cannot do sharing analysis first, since it needs
  -- to be able to look inside 'HOLambda'. On the other hand, if we did
  -- 'HOLambda' reification first (using 'reifyHOAST'), we would destroy the
  -- sharing.



-- | Reifying an n-ary syntactic function to a sharing-preserving 'ASG'
reifyGraph :: Reifiable ctx a dom internal
    => (forall a . HOASTF ctx dom a -> Maybe (Witness' ctx a))
         -- ^ A function that decides whether a given node can be shared.
         -- 'Nothing' means \"don't share\"; 'Just' means \"share\". Nodes whose
         -- result type fulfills @(`Sat` ctx a)@ can be shared, which is why the
         -- function returns a 'Witness''.
    -> a
    -> IO
        ( ASG ctx (Lambda ctx :+: Variable ctx :+: dom) (NAryEval internal)
        , VarId
        )
reifyGraph canShare = reifyGraphHOAST canShare . lambdaN . desugarN

