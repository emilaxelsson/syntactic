{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generic representation of typed syntax trees
--
-- As a simple demonstration, take the following simple language:
--
-- > data Expr1 a
-- >   where
-- >     Num1 :: Int -> Expr1 Int
-- >     Add1 :: Expr1 Int -> Expr1 Int -> Expr1 Int
--
-- Using the present library, this can be rewritten as follows:
--
-- > data Num2 a where Num2 :: Int -> Num2 (Full Int)
-- > data Add2 a where Add2 :: Add2 (Int :-> Int :-> Full Int)
-- >
-- > type Expr2 a = ASTF (Num2 :+: Add2) a
--
-- Note that @Num2@ and @Add2@ are /non-recursive/. The only recursive data type
-- here is 'AST', which is provided by the library. Now, the important point is
-- that @Expr1@ and @Expr2@ are completely isomorphic! This is indicated by the
-- following conversions:
--
-- > conv12 :: Expr1 a -> Expr2 a
-- > conv12 (Num1 n)   = inject (Num2 n)
-- > conv12 (Add1 a b) = inject Add2 :$: conv12 a :$: conv12 b
-- >
-- > conv21 :: Expr2 a -> Expr1 a
-- > conv21 (project -> Just (Num2 n))           = Num1 n
-- > conv21 ((project -> Just Add2) :$: a :$: b) = Add1 (conv21 a) (conv21 b)
--
-- A key property here is that the patterns in @conv21@ are actually complete.
--
-- So, why should one use @Expr2@ instead of @Expr1@? The answer is that @Expr2@
-- can be processed by generic algorithms defined over 'AST', for example:
--
-- > countNodes :: ASTF domain a -> Int
-- > countNodes = count
-- >   where
-- >     count :: AST domain a -> Int
-- >     count (Symbol _) = 1
-- >     count (a :$: b)  = count a + count b
--
-- Furthermore, although @Expr2@ was defined to use exactly the constructors
-- 'Num2' and 'Add2', it is possible to leave the set of constructors open,
-- leading to more modular and reusable code. This can be seen by relaxing the
-- types of @conv12@ and @conv21@:
--
-- > conv12 :: (Num2 :<: dom, Add2 :<: dom) => Expr1 a -> ASTF dom a
-- > conv21 :: (Num2 :<: dom, Add2 :<: dom) => ASTF dom a -> Expr1 a
--
-- This way of encoding open data types is taken from /Data types a la carte/,
-- by Wouter Swierstra, in /Journal of Functional Programming/, 2008. However,
-- we do not need Swierstra's fixed-point machinery for recursive data types.
-- Instead we rely on 'AST' being recursive.

module Language.Syntactic.Syntax
    ( -- * Syntax trees
      Full (..)
    , (:->) (..)
    , ConsType
    , ConsEval
    , EvalResult
    , consEval
    , ($:)
    , AST (..)
    , ASTF
    , (:+:) (..)
      -- * Subsumption
    , (:<:) (..)
      -- * Syntactic sugar
    , Syntactic (..)
    , resugar
      -- * AST processing
    , SubTrees (..)
    , processNode
    ) where



import Data.Typeable



-- | The type of a fully applied constructor
newtype Full a = Full { result :: a }
  deriving (Eq, Show, Typeable)

-- | The type of a partially applied (or unapplied) constructor
newtype a :-> b = Partial (a -> b)
  deriving (Typeable)

infixr :->

-- | Fully or partially applied constructor
--
-- This class is private to the module to guarantee that all members of the
-- class have the form:
--
-- > Full a
-- > a1 :-> Full a2
-- > a1 :-> a2 :-> ... :-> Full an
--
-- The closed class also has the property:
-- @ConsType' (a :-> b)@   iff.   @ConsType' b@.
class ConsType' a
  where
    type ConsEval' a
    type EvalResult' a
    consEval' :: ConsEval' a -> a

instance ConsType' (Full a)
  where
    type ConsEval'   (Full a) = a
    type EvalResult' (Full a) = a
    consEval' = Full

instance ConsType' b => ConsType' (a :-> b)
  where
    type ConsEval'   (a :-> b) = a -> ConsEval' b
    type EvalResult' (a :-> b) = EvalResult' b
    consEval' = Partial . (consEval' .)

-- | Fully or partially applied constructor
--
-- This is a public alias for the hidden class 'ConsType''. The only instances
-- are:
--
-- > instance ConsType' (Full a)
-- > instance ConsType' b => ConsType' (a :-> b)
class    ConsType' a => ConsType a
instance ConsType' a => ConsType a

-- | Maps a 'ConsType' to a simpler form where ':->' has been replaced by @->@,
-- and 'Full' has been removed. This is a public alias for the hidden type
-- 'ConsEval''.
type ConsEval a = ConsEval' a

-- | Returns the result type ('Full' removed) of a 'ConsType'. This is a public
-- alias for the hidden type 'EvalResult''.
type EvalResult a = EvalResult' a

-- | Make a constructor evaluation from a 'ConsEval' representation
consEval :: ConsType a => ConsEval a -> a
consEval = consEval'

-- | Semantic constructor application
($:) :: (a :-> b) -> a -> b
Partial f $: a = f a



-- | Generic abstract syntax tree, parameterized by a symbol domain
--
-- In general, @(`AST` dom (a `:->` b))@ represents a partially applied (or
-- unapplied) constructor, missing at least one argument, while
-- @(`AST` dom (`Full` a))@ represents a fully applied constructor, i.e. a
-- complete syntax tree.
-- It is not possible to construct a total value of type @(`AST` dom a)@ that
-- does not fulfill the constraint @(`ConsType` a)@.
--
-- Note that the hidden class 'ConsType'' mentioned in the type of 'Symbol' is
-- interchangeable with 'ConsType'.
data AST dom a
  where
    Symbol :: ConsType' a => dom a -> AST dom a
    (:$:)  :: Typeable a => AST dom (a :-> b) -> ASTF dom a -> AST dom b

-- | Fully applied abstract syntax tree
type ASTF dom a = AST dom (Full a)

-- | Co-product of two symbol domains
data dom1 :+: dom2 :: * -> *
  where
    InjectL :: dom1 a -> (dom1 :+: dom2) a
    InjectR :: dom2 a -> (dom1 :+: dom2) a

infixl 1 :$:
infixr :+:



class sub :<: sup
  where
    -- | Injection from @sub@ to @sup@
    inject :: ConsType a => sub a -> sup a

    -- | Partial projection from @sup@ to @sub@
    project :: sup a -> Maybe (sub a)

instance (sub :<: sup) => ((:<:) sub (AST sup))
                            -- GHC 6.12 requires prefix syntax here
  where
    inject = Symbol . inject

    project (Symbol a) = project a
    project _          = Nothing

instance ((:<:) expr expr)
  where
    inject  = id
    project = Just

instance ((:<:) expr1 (expr1 :+: expr2))
  where
    inject = InjectL

    project (InjectL a) = Just a
    project _           = Nothing

instance (expr1 :<: expr3) => ((:<:) expr1 (expr2 :+: expr3))
  where
    inject = InjectR . inject

    project (InjectR a) = project a
    project _           = Nothing



-- | It is assumed that for all types @A@ fulfilling @(`Syntactic` A dom)@:
--
-- > eval a == eval (desugar $ (id :: A -> A) $ sugar a)
--
-- (using 'Language.Syntactic.Analysis.Evaluation.eval')
class Typeable (Internal a) => Syntactic a dom | a -> dom
    -- Note: using a two-parameter class rather than an associated type, because
    -- this makes it possible to make a class alias constraining dom. GHC
    -- doesn't yet handle equality super classes.
  where
    type Internal a
    desugar :: a -> ASTF dom (Internal a)
    sugar   :: ASTF dom (Internal a) -> a

instance Typeable a => Syntactic (ASTF dom a) dom
  where
    type Internal (ASTF dom a) = a
    desugar = id
    sugar   = id

-- | Syntactic type casting
resugar :: (Syntactic a dom, Syntactic b dom, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar



-- | Data family for collecting the children of a constructor, for example:
--
-- > subTrees :: forall dom . SubTrees dom (Int :-> Bool :-> Full [Int])
-- > subTrees = a :*: b :*: Nil
-- >   where
-- >     a = undefined :: ASTF dom Int
-- >     b = undefined :: ASTF dom Bool
--
-- @(`SubTrees` a)@ is meaningful iff. @(`ConsType` a)@
data family SubTrees (dom :: * -> *) a

data instance SubTrees dom (Full a)  = Nil
data instance SubTrees dom (a :-> b) = ASTF dom a :*: SubTrees dom b

infixr :*:

-- | Process an 'AST' using a function that gets direct access to the top-most
-- constructor and its sub-trees
--
-- This function can be used to create 'AST' traversal functions indexed by the
-- symbol types, for example:
--
-- > class Count subDomain
-- >   where
-- >     count' :: Count domain => subDomain a -> SubTrees domain a -> Int
-- >
-- > instance (Count sub1, Count sub2) => Count (sub1 :+: sub2)
-- >   where
-- >     count' (InjectL a) args = count' a args
-- >     count' (InjectR a) args = count' a args
-- >
-- > count :: Count dom => ASTF dom a -> Int
-- > count = processNode count'
--
-- Here, @count@ represents some static analysis on an 'AST'. Each constructor
-- in the tree will be processed by @count'@ indexed by the corresponding symbol
-- type. That way, @count'@ can be seen as an open-ended function on an open
-- data type. The @(Count domain)@ constraint on @count'@ is to allow recursion
-- over sub-trees.
--
-- Let's say we have a symbol
--
-- > data Add a
-- >   where
-- >     Add :: Add (Int :-> Int :-> Full Int)
--
-- Then the @Count@ instance for @Add@ might look as follows:
--
-- > instance Count Add
-- >   where
-- >     count' Add (a :*: b :*: Nil) = 1 + count a + count b
processNode :: forall dom a b
    .  (forall a . ConsType a => dom a -> SubTrees dom a -> b)
    -> ASTF dom a -> b
processNode f a = process a Nil
  where
    process :: AST dom c -> SubTrees dom c -> b
    process (Symbol a) args = f a args
    process (c :$: a)  args = process c (a :*: args)

