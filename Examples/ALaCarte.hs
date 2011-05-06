{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Demonstration of the fact that "Language.Syntactic" has the same
-- functionality as /Data types a la carte/ (Wouter Swierstra, in
-- /Journal of Functional Programming/, 2008)

module ALaCarte where



import Language.Syntactic



data Val a
  where
    Val :: Int -> Val (Full Int)

data Add a
  where
    Add :: Add (Int :-> Int :-> Full Int)

data Mul a
  where
    Mul :: Mul (Int :-> Int :-> Full Int)

instance Eval Val
  where
    evaluate (Val a) = Full a

instance Eval Add
  where
    evaluate Add = Partial $ \a -> Partial $ \b -> Full (a+b)

instance Eval Mul
  where
    evaluate Mul = Partial $ \a -> Partial $ \b -> Full (a*b)

instance Render Val
  where
    render (Val a) = show a

instance Render Add
  where
    render Add = "(+)"

instance Render Mul
  where
    render Mul = "(*)"



-- Manual injection:

addExample :: ASTF (Val :+: Add) Int
addExample = Symbol (InjectR Add) :$: Symbol (InjectL (Val 118)) :$: Symbol (InjectL (Val 1219))



-- Automatic injection:

val :: (Val :<: expr) => Int -> ASTF expr Int
val = inject . Val

(<+>) :: (Add :<: expr) => ASTF expr Int -> ASTF expr Int -> ASTF expr Int
a <+> b = inject Add :$: a :$: b

(<*>) :: (Mul :<: expr) => ASTF expr Int -> ASTF expr Int -> ASTF expr Int
a <*> b = inject Mul :$: a :$: b

infixl 6 <+>
infixl 7 <*>

example1 :: ASTF (Add :+: Val) Int
example1 = val 30000 <+> val 1330 <+> val 7

test1 = evaluate example1

example2 :: ASTF (Val :+: Add :+: Mul) Int
example2 = val 80 <*> val 5 <+> val 4

test2 = evaluate example2

example3 :: ASTF (Val :+: Mul) Int
example3 = val 6 <*> val 7

test3 = evaluate example3

example4 :: ASTF (Val :+: Add :+: Mul) Int
example4 = val 80 <*> val 5 <+> val 4

test4 = render example4



-- Pattern matching:

distr :: (Add :<: expr, Mul :<: expr, ConsType a) => AST expr a -> AST expr a
distr ((project -> Just Mul) :$: a :$: b) = case distr b of
    (project -> Just Add) :$: c :$: d -> a' <*> c <+> a' <*> d
    b' -> a' <*> b'
  where
    a' = distr a
distr (f :$: a) = distr f :$: distr a
distr a         = a
  -- Note the use of direct recursion instead of a fold combinator

example5 :: ASTF (Val :+: Add :+: Mul) Int
example5 = val 80 <*> (val 5 <+> val 4) <+> val 543

test5 = render (distr example5)

example6 :: ASTF (Mul :+: Add :+: Val) Int
example6 = val 444 <*> (val 80 <*> (val 5 <+> val 3 <*> val 4))

test6 = render (distr example6)

