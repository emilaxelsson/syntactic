-- | Generic traversals of 'AST' terms

module Language.Syntactic.Traversal
    ( gmapQ
    , gmapT
    , everywhereUp
    , everywhereDown
    , universe
    , Args (..)
    , listArgs
    , mapArgs
    , mapArgsA
    , mapArgsM
    , foldrArgs
    , appArgs
    , listFold
    , match
    , simpleMatch
    , fold
    , simpleFold
    , matchTrans
    , mapAST
    , WrapFull (..)
    , toTree
    ) where



import Control.Applicative
import Data.Tree

import Language.Syntactic.Syntax



-- | Map a function over all immediate sub-terms (corresponds to the function
-- with the same name in Scrap Your Boilerplate)
gmapT :: forall sym
      .  (forall a . ASTF sym a -> ASTF sym a)
      -> (forall a . ASTF sym a -> ASTF sym a)
gmapT f a = go a
  where
    go :: AST sym a -> AST sym a
    go (s :$ a) = go s :$ f a
    go s        = s

-- | Map a function over all immediate sub-terms, collecting the results in a
-- list (corresponds to the function with the same name in Scrap Your
-- Boilerplate)
gmapQ :: forall sym b
      .  (forall a . ASTF sym a -> b)
      -> (forall a . ASTF sym a -> [b])
gmapQ f a = go a
  where
    go :: AST sym a -> [b]
    go (s :$ a) = f a : go s
    go _        = []

-- | Apply a transformation bottom-up over an 'AST' (corresponds to @everywhere@ in Scrap Your
-- Boilerplate)
everywhereUp
    :: (forall a . ASTF sym a -> ASTF sym a)
    -> (forall a . ASTF sym a -> ASTF sym a)
everywhereUp f = f . gmapT (everywhereUp f)

-- | Apply a transformation top-down over an 'AST' (corresponds to @everywhere'@ in Scrap Your
-- Boilerplate)
everywhereDown
    :: (forall a . ASTF sym a -> ASTF sym a)
    -> (forall a . ASTF sym a -> ASTF sym a)
everywhereDown f = gmapT (everywhereDown f) . f

-- | List all sub-terms (corresponds to @universe@ in Uniplate)
universe :: ASTF sym a -> [EF (AST sym)]
universe a = EF a : go a
  where
    go :: AST sym a -> [EF (AST sym)]
    go (Sym s)  = []
    go (s :$ a) = go s ++ universe a

-- | List of symbol arguments
data Args c sig
  where
    Nil  :: Args c (Full a)
    (:*) :: c (Full a) -> Args c sig -> Args c (a :-> sig)

infixr :*

-- | Map a function over an 'Args' list and collect the results in an ordinary list
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
appArgs :: AST sym sig -> Args (AST sym) sig -> ASTF sym (DenResult sig)
appArgs a Nil       = a
appArgs s (a :* as) = appArgs (s :$ a) as

-- | \"Pattern match\" on an 'AST' using a function that gets direct access to
-- the top-most symbol and its sub-trees
match :: forall sym a c
    .  ( forall sig . (a ~ DenResult sig) =>
           sym sig -> Args (AST sym) sig -> c (Full a)
       )
    -> ASTF sym a
    -> c (Full a)
match f a = go a Nil
  where
    go :: (a ~ DenResult sig) => AST sym sig -> Args (AST sym) sig -> c (Full a)
    go (Sym a)  as = f a as
    go (s :$ a) as = go s (a :* as)

-- | A version of 'match' with a simpler result type
simpleMatch :: forall sym a b
    .  (forall sig . (a ~ DenResult sig) => sym sig -> Args (AST sym) sig -> b)
    -> ASTF sym a
    -> b
simpleMatch f = getConst . match (\s -> Const . f s)

-- | Fold an 'AST' using an 'Args' list to hold the results of sub-terms
fold :: forall sym c
    .  (forall sig . sym sig -> Args c sig -> c (Full (DenResult sig)))
    -> (forall a   . ASTF sym a -> c (Full a))
fold f = match (\s -> f s . mapArgs (fold f))

-- | Simplified version of 'fold' for situations where all intermediate results
-- have the same type
simpleFold :: forall sym b
    .  (forall sig . sym sig -> Args (Const b) sig -> b)
    -> (forall a   . ASTF sym a                    -> b)
simpleFold f = getConst . fold (\s -> Const . f s)

-- | Fold an 'AST' using a list to hold the results of sub-terms
listFold :: forall sym b
    .  (forall sig . sym sig -> [b] -> b)
    -> (forall a   . ASTF sym a     -> b)
listFold f = simpleFold (\s -> f s . listArgs getConst)

newtype WrapAST c sym sig = WrapAST { unWrapAST :: c (AST sym sig) }
  -- Only used in the definition of 'matchTrans'

-- | A version of 'match' where the result is a transformed syntax tree,
-- wrapped in a type constructor @c@
matchTrans :: forall sym sym' c a
    .  ( forall sig . (a ~ DenResult sig) =>
           sym sig -> Args (AST sym) sig -> c (ASTF sym' a)
       )
    -> ASTF sym a
    -> c (ASTF sym' a)
matchTrans f = unWrapAST . match (\s -> WrapAST . f s)

-- | Update the symbols in an AST
mapAST :: (forall sig' . sym1 sig' -> sym2 sig') -> AST sym1 sig -> AST sym2 sig
mapAST f (Sym s)  = Sym (f s)
mapAST f (s :$ a) = mapAST f s :$ mapAST f a

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

-- | Convert an 'AST' to a 'Tree'
toTree :: forall dom a b . (forall sig . dom sig -> b) -> ASTF dom a -> Tree b
toTree f = listFold (Node . f)

