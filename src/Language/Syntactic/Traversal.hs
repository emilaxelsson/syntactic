-- | Generic traversals of 'AST' terms

module Language.Syntactic.Traversal
    ( gmapQ
    , gmapT
    , everywhereUp
    , everywhereDown
    , Args (..)
    , listArgs
    , mapArgs
    , mapArgsA
    , mapArgsM
    , appArgs
    , listFold
    , match
    , query
    , simpleMatch
    , fold
    , simpleFold
    , matchTrans
    , WrapFull (..)
    ) where



import Control.Applicative

import Language.Syntactic.Syntax



-- | Map a function over all immediate sub-terms (corresponds to the function
-- with the same name in Scrap Your Boilerplate)
gmapT :: forall dom
      .  (forall a . ASTF dom a -> ASTF dom a)
      -> (forall a . ASTF dom a -> ASTF dom a)
gmapT f a = go a
  where
    go :: forall a . AST dom a -> AST dom a
    go (s :$ a) = go s :$ f a
    go s        = s

-- | Map a function over all immediate sub-terms, collecting the results in a
-- list (corresponds to the function with the same name in Scrap Your
-- Boilerplate)
gmapQ :: forall dom b
      .  (forall a . ASTF dom a -> b)
      -> (forall a . ASTF dom a -> [b])
gmapQ f a = go a
  where
    go :: forall a . AST dom a -> [b]
    go (s :$ a) = f a : go s
    go _        = []

-- | Apply a transformation bottom-up over an expression (corresponds to
-- @everywhere@ in Scrap Your Boilerplate)
everywhereUp
    :: (forall a . ASTF dom a -> ASTF dom a)
    -> (forall a . ASTF dom a -> ASTF dom a)
everywhereUp f = f . gmapT (everywhereUp f)

-- | Apply a transformation top-down over an expression (corresponds to
-- @everywhere'@ in Scrap Your Boilerplate)
everywhereDown
    :: (forall a . ASTF dom a -> ASTF dom a)
    -> (forall a . ASTF dom a -> ASTF dom a)
everywhereDown f = gmapT (everywhereDown f) . f

-- | List of symbol arguments
data Args c sig
  where
    Nil  :: Args c (Full a)
    (:*) :: c (Full a) -> Args c sig -> Args c (a :-> sig)

infixr :*

-- | Map a function over an 'Args' list and collect the results in an ordinary
-- list
listArgs :: (forall a . c (Full a) -> b) -> Args c sig -> [b]
listArgs f Nil       = []
listArgs f (a :* as) = f a : listArgs f as

-- | Map a function over an 'Args' list
mapArgs
    :: (forall a   . c1 (Full a) -> c2 (Full a))
    -> (forall sig . Args c1 sig -> Args c2 sig)
mapArgs f Nil       = Nil
mapArgs f (a :* as) = f a :* mapArgs f as

-- | Map an applicative function over an 'Args' list
mapArgsA :: Applicative f
    => (forall a   . c1 (Full a) -> f (c2 (Full a)))
    -> (forall sig . Args c1 sig -> f (Args c2 sig))
mapArgsA f Nil       = pure Nil
mapArgsA f (a :* as) = (:*) <$> f a <*> mapArgsA f as

-- | Map a monadic function over an 'Args' list
mapArgsM :: Monad m
    => (forall a   . c1 (Full a) -> m (c2 (Full a)))
    -> (forall sig . Args c1 sig -> m (Args c2 sig))
mapArgsM f = unwrapMonad . mapArgsA (WrapMonad . f)

-- | Right fold for an 'Args' list
foldrArgs
    :: (forall a . c (Full a) -> b -> b)
    -> b
    -> (forall sig . Args c sig -> b)
foldrArgs f b Nil       = b
foldrArgs f b (a :* as) = f a (foldrArgs f b as)

-- | Apply a (partially applied) symbol to a list of argument terms
appArgs :: AST dom sig -> Args (AST dom) sig -> ASTF dom (DenResult sig)
appArgs a Nil       = a
appArgs s (a :* as) = appArgs (s :$ a) as

-- | \"Pattern match\" on an 'AST' using a function that gets direct access to
-- the top-most symbol and its sub-trees
match :: forall dom a c
    .  ( forall sig . (a ~ DenResult sig) =>
           dom sig -> Args (AST dom) sig -> c (Full a)
       )
    -> ASTF dom a
    -> c (Full a)
match f a = go a Nil
  where
    go :: (a ~ DenResult sig) => AST dom sig -> Args (AST dom) sig -> c (Full a)
    go (Sym a)  as = f a as
    go (s :$ a) as = go s (a :* as)

query :: forall dom a c
    .  ( forall sig . (a ~ DenResult sig) =>
           dom sig -> Args (AST dom) sig -> c (Full a)
       )
    -> ASTF dom a
    -> c (Full a)
query = match
{-# DEPRECATED query "Please use `match` instead." #-}

-- | A version of 'match' with a simpler result type
simpleMatch :: forall dom a b
    .  (forall sig . (a ~ DenResult sig) => dom sig -> Args (AST dom) sig -> b)
    -> ASTF dom a
    -> b
simpleMatch f = getConst . match (\s -> Const . f s)

-- | Fold an 'AST' using an 'Args' list to hold the results of sub-terms
fold :: forall dom c
    .  (forall sig . dom sig -> Args c sig -> c (Full (DenResult sig)))
    -> (forall a   . ASTF dom a -> c (Full a))
fold f = match (\s -> f s . mapArgs (fold f))

-- | Simplified version of 'fold' for situations where all intermediate results
-- have the same type
simpleFold :: forall dom b
    .  (forall sig . dom sig -> Args (Const b) sig -> b)
    -> (forall a   . ASTF dom a                    -> b)
simpleFold f = getConst . fold (\s -> Const . f s)

-- | Fold an 'AST' using a list to hold the results of sub-terms
listFold :: forall dom b
    .  (forall sig . dom sig -> [b] -> b)
    -> (forall a   . ASTF dom a     -> b)
listFold f = simpleFold (\s -> f s . listArgs getConst)

newtype WrapAST c dom sig = WrapAST { unWrapAST :: c (AST dom sig) }
  -- Only used in the definition of 'matchTrans'

-- | A version of 'match' where the result is a transformed syntax tree,
-- wrapped in a type constructor @c@
matchTrans :: forall dom dom' c a
    .  ( forall sig . (a ~ DenResult sig) =>
           dom sig -> Args (AST dom) sig -> c (ASTF dom' a)
       )
    -> ASTF dom a
    -> c (ASTF dom' a)
matchTrans f = unWrapAST . match (\s -> WrapAST . f s)

-- | Can be used to make an arbitrary type constructor indexed by @(`Full` a)@.
-- This is useful as the type constructor parameter of 'Args'. That is, use
--
-- > Args (WrapFull c) ...
--
-- instead of
--
-- > Args c ...
--
-- if @c@ is not indexed by @(`Full` a)@.
data WrapFull c a
  where
    WrapFull :: { unwrapFull :: c a } -> WrapFull c (Full a)

