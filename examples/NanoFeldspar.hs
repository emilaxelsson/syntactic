{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

-- | A minimal Feldspar core language implementation. The intention of this
-- module is to demonstrate how to quickly make a language prototype using
-- syntactic.

module NanoFeldspar where



import Prelude hiding
    ( length, max, min, not, (==)
    , map, sum, zip, zipWith
    )
import qualified Prelude

import Data.Tree

import Data.Syntactic hiding (fold, printExpr, showAST, drawAST, writeHtmlAST)
import qualified Data.Syntactic as Syntactic



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Convenient class alias
class    (Ord a, Show a) => Type a
instance (Ord a, Show a) => Type a

type Length = Int
type Index  = Int



--------------------------------------------------------------------------------
-- * Abstract syntax
--------------------------------------------------------------------------------

data Arithmetic a
  where
    Literal :: (Type a, Num a) => a -> Arithmetic (Full a)
    Add     :: (Type a, Num a) => Arithmetic (a :-> a :-> Full a)
    Sub     :: (Type a, Num a) => Arithmetic (a :-> a :-> Full a)
    Mul     :: (Type a, Num a) => Arithmetic (a :-> a :-> Full a)

instance Semantic Arithmetic
  where
    semantics (Literal a) = Sem (show a) a
    semantics Add         = Sem "(+)" (+)
    semantics Sub         = Sem "(-)" (-)
    semantics Mul         = Sem "(*)" (*)

semanticInstances ''Arithmetic



type Name = Integer

data Binding a
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

instance Render Binding
  where
    renderSym (Var n) = 'v' : show n
    renderSym (Lam n) = "Lam v" ++ show n
    renderArgs []     (Var n) = 'v' : show n
    renderArgs [body] (Lam n) = "(\\" ++ ('v':show n) ++ " -> " ++ body ++ ")"

instance StringTree Binding
  where
    stringTreeSym []     (Var n) = Node ('v' : show n) []
    stringTreeSym [body] (Lam n) = Node ("Lam " ++ 'v' : show n) [body]

maxLam :: (Binding :<: s) => AST s a -> Name
maxLam (Sym lam :$ _) | Just (Lam n) <- prj lam = n
maxLam (s :$ a) = maxLam s `Prelude.max` maxLam a
maxLam _ = 0

lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = appSym (Lam n) body
  where
    body = f (appSym (Var n))
    n    = succ (maxLam body)
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)



data Parallel a
  where
    Parallel :: Type a => Parallel (Length :-> (Index -> a) :-> Full [a])

instance Semantic Parallel
  where
    semantics Parallel = Sem
        { semanticName = "parallel"
        , semanticEval = \len ixf -> Prelude.map ixf [0 .. len-1]
        }

semanticInstances ''Parallel



data ForLoop a
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance Semantic ForLoop
  where
    semantics ForLoop = Sem
        { semanticName = "forLoop"
        , semanticEval = \len init body -> foldl (flip body) init [0 .. len-1]
        }

semanticInstances ''ForLoop



instance StringTree Semantics

type FeldDomain
    =   Arithmetic
    :+: Binding
    :+: Parallel
    :+: ForLoop
    :+: Semantics
  -- We're cheating a bit by using `Semantics` as a symbol to represent literals and primitive
  -- functions. The proper way would be to define new symbol types similarly to `Arithmetic`.

newtype Data a = Data { unData :: ASTF FeldDomain a }

-- | Declaring 'Data' as syntactic sugar
instance Type a => Syntactic (Data a)
  where
    type Domain (Data a)   = FeldDomain
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class    (Syntactic a, Domain a ~ FeldDomain, Type (Internal a)) => Syntax a
instance (Syntactic a, Domain a ~ FeldDomain, Type (Internal a)) => Syntax a

instance Type a => Show (Data a)
  where
    show (Data a) = render a



--------------------------------------------------------------------------------
-- * Rendering
--------------------------------------------------------------------------------

-- | Show the expression
showExpr :: (Syntactic a, Domain a ~ FeldDomain) => a -> String
showExpr = render . desugar

-- | Print the expression
printExpr :: (Syntactic a, Domain a ~ FeldDomain) => a -> IO ()
printExpr = putStrLn . showExpr

-- | Show the syntax tree using unicode art
showAST :: (Syntactic a, Domain a ~ FeldDomain) => a -> String
showAST = Syntactic.showAST . desugar

-- | Draw the syntax tree on the terminal using unicode art
drawAST :: (Syntactic a, Domain a ~ FeldDomain) => a -> IO ()
drawAST = putStrLn . showAST

-- | Write the syntax tree to an HTML file with foldable nodes
writeHtmlAST :: (Syntactic a, Domain a ~ FeldDomain) => a -> IO ()
writeHtmlAST = Syntactic.writeHtmlAST "tree.html" . desugar



--------------------------------------------------------------------------------
-- * Front end
--------------------------------------------------------------------------------

-- | Literal
value :: Syntax a => Internal a -> a
value a = sugar $ appSym $ Sem (show a) a

false :: Data Bool
false = value False

true :: Data Bool
true = value True

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = sugarSym . Literal . fromInteger
    (+)         = sugarSym Add
    (-)         = sugarSym Sub
    (*)         = sugarSym Mul

instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Binding :<: dom
    ) =>
      Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lam (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = sugarSymC Parallel

-- | For loop
forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSymC ForLoop

(?) :: forall a . Syntax a => Data Bool -> (a,a) -> a
c ? (t,f) = sugarSym sym c t f
  where
    sym :: Semantics (Bool :-> Internal a :-> Internal a :-> Full (Internal a))
    sym = Sem "cond" (\c t f -> if c then t else f)

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarSym $ Sem "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSym $ Sem "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

not :: Data Bool -> Data Bool
not = sugarSym $ Sem "not" Prelude.not

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSym $ Sem "(==)" (Prelude.==)

max :: Type a => Data a -> Data a -> Data a
max = sugarSym $ Sem "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarSym $ Sem "min" Prelude.min



--------------------------------------------------------------------------------
-- * Vector library
--------------------------------------------------------------------------------

data Vector a
  where
    Indexed :: Data Length -> (Data Index -> a) -> Vector a

instance Syntax a => Syntactic (Vector a)
  where
    type Domain (Vector a)   = FeldDomain
    type Internal (Vector a) = [Internal a]
    desugar = desugar . freezeVector . map resugar
    sugar   = map resugar . thawVector . sugar

length :: Vector a -> Data Length
length (Indexed len _) = len

indexed :: Data Length -> (Data Index -> a) -> Vector a
indexed = Indexed

index :: Vector a -> Data Index -> a
index (Indexed _ ixf) = ixf

(!) :: Vector a -> Data Index -> a
Indexed _ ixf ! i = ixf i

infixl 9 !

freezeVector :: Type a => Vector (Data a) -> Data [a]
freezeVector vec = parallel (length vec) (index vec)

thawVector :: Type a => Data [a] -> Vector (Data a)
thawVector arr = Indexed (arrLength arr) (getIx arr)

zip :: Vector a -> Vector b -> Vector (a,b)
zip a b = indexed (length a `min` length b) (\i -> (index a i, index b i))

unzip :: Vector (a,b) -> (Vector a, Vector b)
unzip ab = (indexed len (fst . index ab), indexed len (snd . index ab))
  where
    len = length ab

permute :: (Data Length -> Data Index -> Data Index) -> (Vector a -> Vector a)
permute perm vec = indexed len (index vec . perm len)
  where
    len = length vec

reverse :: Vector a -> Vector a
reverse = permute $ \len i -> len-i-1

(...) :: Data Index -> Data Index -> Vector (Data Index)
l ... h = indexed (h-l+1) (+l)

map :: (a -> b) -> Vector a -> Vector b
map f (Indexed len ixf) = Indexed len (f . ixf)

zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith f a b = map (uncurry f) $ zip a b

fold :: Syntax b => (a -> b -> b) -> b -> Vector a -> b
fold f b (Indexed len ixf) = forLoop len b (\i st -> f (ixf i) st)

sum :: (Num a, Syntax a) => Vector a -> a
sum = fold (+) 0

type Matrix a = Vector (Vector (Data a))

-- | Transpose of a matrix. Assumes that the number of rows is > 0.
transpose :: Type a => Matrix a -> Matrix a
transpose a = indexed (length (a!0)) $ \k -> indexed (length a) $ \l -> a ! l ! k



--------------------------------------------------------------------------------
-- * Examples
--------------------------------------------------------------------------------

scProd :: Vector (Data Float) -> Vector (Data Float) -> Data Float
scProd a b = sum (zipWith (*) a b)

forEach = flip map

-- Matrix multiplication
matMul :: Matrix Float -> Matrix Float -> Matrix Float
matMul a b = forEach a $ \a' ->
               forEach (transpose b) $ \b' ->
                 scProd a' b'

