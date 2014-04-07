{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | A minimal Feldspar core language implementation. The intention of this
-- module is to demonstrate how to quickly make a language prototype using
-- syntactic.
--
-- A more realistic implementation would use custom contexts to restrict the
-- types at which constructors operate. Currently, all general constructs (such
-- as 'Literal' and 'Tuple') use a 'SimpleCtx' context, which means that the
-- types are quite unrestricted. A real implementation would also probably use
-- custom types for primitive functions, since 'Construct' is quite unsafe (uses
-- only a 'String' to distinguish between functions).

module NanoFeldspar.Core where



import Data.Typeable

import Language.Syntactic as Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Condition
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Constructs.Tuple
import Language.Syntactic.Frontend.Tuple
import Language.Syntactic.Sharing.SimpleCodeMotion
import Language.Syntactic.Sharing.CodeMotion2



--------------------------------------------------------------------------------
-- * Types
--------------------------------------------------------------------------------

-- | Convenient class alias
class    (Ord a, Show a, Typeable a) => Type a
instance (Ord a, Show a, Typeable a) => Type a

type Length = Int
type Index  = Int



--------------------------------------------------------------------------------
-- * Parallel arrays
--------------------------------------------------------------------------------

data Parallel a
  where
    Parallel :: Type a => Parallel (Length :-> (Index -> a) :-> Full [a])

instance Constrained Parallel
  where
    type Sat Parallel = Type
    exprDict Parallel = Dict

instance Semantic Parallel
  where
    semantics Parallel = Sem
        { semanticName = "parallel"
        , semanticEval = \len ixf -> map ixf [0 .. len-1]
        }

semanticInstances ''Parallel

instance EvalBind Parallel where evalBindSym = evalBindSymDefault

instance AlphaEq dom dom dom env => AlphaEq Parallel Parallel dom env
  where
    alphaEqSym = alphaEqSymDefault



--------------------------------------------------------------------------------
-- * For loops
--------------------------------------------------------------------------------

data ForLoop a
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance Constrained ForLoop
  where
    type Sat ForLoop = Type
    exprDict ForLoop = Dict

instance Semantic ForLoop
  where
    semantics ForLoop = Sem
        { semanticName = "forLoop"
        , semanticEval = \len init body -> foldl (flip body) init [0 .. len-1]
        }

semanticInstances ''ForLoop

instance EvalBind ForLoop where evalBindSym = evalBindSymDefault

instance AlphaEq dom dom dom env => AlphaEq ForLoop ForLoop dom env
  where
    alphaEqSym = alphaEqSymDefault



--------------------------------------------------------------------------------
-- * Feldspar domain
--------------------------------------------------------------------------------

-- | The Feldspar domain
type FeldDomain
    =   Construct
    :+: Literal
    :+: Condition
    :+: Tuple
    :+: Select
    :+: Parallel
    :+: ForLoop

type FeldSyms      = Let :+: (FeldDomain :|| Eq :| Show)
type FeldDomainAll = HODomain FeldSyms Typeable Top

newtype Data a = Data { unData :: ASTF FeldDomainAll a }

-- | Declaring 'Data' as syntactic sugar
instance Type a => Syntactic (Data a)
  where
    type Domain (Data a)   = FeldDomainAll
    type Internal (Data a) = a
    desugar = unData
    sugar   = Data

-- | Specialization of the 'Syntactic' class for the Feldspar domain
class    (Syntactic a, Domain a ~ FeldDomainAll, Type (Internal a)) => Syntax a
instance (Syntactic a, Domain a ~ FeldDomainAll, Type (Internal a)) => Syntax a

-- | A predicate deciding which constructs can be shared. Lambdas and literals are not shared.
canShare :: ASTF (FODomain FeldSyms Typeable Top) a -> Maybe (Dict (Top a))
canShare (lam :$ _)
    | Just _ <- prjP (P::P (CLambda Top)) lam = Nothing
canShare (prj -> Just (Literal _)) = Nothing
canShare _  = Just Dict

canShareIn :: ASTF (FODomain FeldSyms Typeable Top) a -> Bool
canShareIn (lam :$ _)
    | Just _ <- prjP (P::P (CLambda Top)) lam = False
canShareIn _ = True

canShareDict :: MkInjDict (FODomain FeldSyms Typeable Top)
canShareDict = mkInjDictFO canShare canShareIn

canShareDict2 :: MkInjDict (FODomain FeldSyms Typeable Top)
canShareDict2 = mkInjDictFO canShare (const True)



--------------------------------------------------------------------------------
-- * Back ends
--------------------------------------------------------------------------------

-- | Show the expression
showExpr :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> String
showExpr = render . reifySmart (const True) canShareDict

-- | Print the expression
printExpr :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> IO ()
printExpr = print . reifySmart (const True) canShareDict

-- | Show the syntax tree using Unicode art
showAST :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> String
showAST = Syntactic.showAST . reifySmart (const True) canShareDict

showAST2 :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> String
showAST2 = Syntactic.showAST . reifySmart2 (const True) canShareDict

-- | Draw the syntax tree on the terminal using Unicode art
drawAST :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> IO ()
drawAST = Syntactic.drawAST . reifySmart (const True) canShareDict

-- | Write the syntax tree to an HTML file with foldable nodes
writeHtmlAST :: (Syntactic a, Domain a ~ FeldDomain) => a -> IO ()
writeHtmlAST = Syntactic.writeHtmlAST "tree.html" . desugar

-- | Evaluation
eval :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> Internal a
eval = evalBind . reifySmart (const True) canShareDict

eval2 :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> Internal a
eval2 = evalBind . reifySmart2 (const True) canShareDict2



--------------------------------------------------------------------------------
-- * Core library
--------------------------------------------------------------------------------

-- | Literal
value :: Syntax a => Internal a -> a
value = sugarSymC . Literal

false :: Data Bool
false = value False

true :: Data Bool
true = value True

-- | For types containing some kind of \"thunk\", this function can be used to
-- force computation
force :: Syntax a => a -> a
force = resugar

-- | Share a value using let binding
share :: (Syntax a, Syntax b) => a -> (a -> b) -> b
share = sugarSymC Let

-- | Alpha equivalence
instance Type a => Eq (Data a)
  where
    Data a == Data b = alphaEq (reify a) (reify b)

instance Type a => Show (Data a)
  where
    show (Data a) = render $ reify a

instance (Type a, Num a) => Num (Data a)
  where
    fromInteger = value . fromInteger
    abs         = sugarSymC $ Construct "abs" abs
    signum      = sugarSymC $ Construct "signum" signum
    (+)         = sugarSymC $ Construct "(+)" (+)
    (-)         = sugarSymC $ Construct "(-)" (-)
    (*)         = sugarSymC $ Construct "(*)" (*)

(?) :: Syntax a => Data Bool -> (a,a) -> a
cond ? (t,e) = sugarSymC Condition cond t e

-- | Parallel array
parallel :: Type a => Data Length -> (Data Index -> Data a) -> Data [a]
parallel = sugarSymC Parallel

forLoop :: Syntax st => Data Length -> st -> (Data Index -> st -> st) -> st
forLoop = sugarSymC ForLoop

arrLength :: Type a => Data [a] -> Data Length
arrLength = sugarSymC $ Construct "arrLength" Prelude.length

-- | Array indexing
getIx :: Type a => Data [a] -> Data Index -> Data a
getIx = sugarSymC $ Construct "getIx" eval
  where
    eval as i
        | i >= len || i < 0 = error "getIx: index out of bounds"
        | otherwise         = as !! i
      where
        len = Prelude.length as

not :: Data Bool -> Data Bool
not = sugarSymC $ Construct "not" Prelude.not

(==) :: Type a => Data a -> Data a -> Data Bool
(==) = sugarSymC $ Construct "(==)" (Prelude.==)

max :: Type a => Data a -> Data a -> Data a
max = sugarSymC $ Construct "max" Prelude.max

min :: Type a => Data a -> Data a -> Data a
min = sugarSymC $ Construct "min" Prelude.min

