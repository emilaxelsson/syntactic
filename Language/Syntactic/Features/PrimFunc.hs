-- | Primitive functions

module Language.Syntactic.Features.PrimFunc where



import Data.Typeable

import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash



data PrimFunc a
  where
    PrimFunc :: ConsType b =>
        String -> (ConsEval (a :-> b)) -> PrimFunc (a :-> b)

instance ExprEq PrimFunc
  where
    PrimFunc f1 _ `exprEq` PrimFunc f2 _ = f1==f2

instance Render PrimFunc
  where
    renderPart [] (PrimFunc name _) = name
    renderPart args (PrimFunc name _)
        | isInfix   = "(" ++ unwords [a,op,b] ++ ")"
        | otherwise = "(" ++ unwords (name : args) ++ ")"
      where
        [a,b] = args
        op    = init $ tail name
        isInfix
          =  not (null name)
          && head name == '('
          && last name == ')'
          && length args == 2

instance ToTree PrimFunc

instance Eval PrimFunc
  where
    evaluate (PrimFunc _ f) = consEval f

instance ExprHash PrimFunc
  where
    exprHash (PrimFunc name _) = hash name



primFunc :: (Typeable a, PrimFunc :<: expr)
    => String
    -> (a -> b)
    -> ASTF expr a
    -> ASTF expr b
primFunc name f a = inject (PrimFunc name f) :$: a

primFunc2 :: (Typeable a, Typeable b, PrimFunc :<: expr)
    => String
    -> (a -> b -> c)
    -> ASTF expr a
    -> ASTF expr b
    -> ASTF expr c
primFunc2 name f a b = inject (PrimFunc name f) :$: a :$: b

primFunc3 :: (Typeable a, Typeable b, Typeable c, PrimFunc :<: expr)
    => String
    -> (a -> b -> c -> d)
    -> ASTF expr a
    -> ASTF expr b
    -> ASTF expr c
    -> ASTF expr d
primFunc3 name f a b c = inject (PrimFunc name f) :$: a :$: b :$: c

primFunc4 :: (Typeable a, Typeable b, Typeable c, Typeable d, PrimFunc :<: expr)
    => String
    -> (a -> b -> c -> d -> e)
    -> ASTF expr a
    -> ASTF expr b
    -> ASTF expr c
    -> ASTF expr d
    -> ASTF expr e
primFunc4 name f a b c d = inject (PrimFunc name f) :$: a :$: b :$: c :$: d

