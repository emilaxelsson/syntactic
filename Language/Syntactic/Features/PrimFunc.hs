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



primFunc :: (Typeable a, PrimFunc :<: dom)
    => String
    -> (a -> b)
    -> ASTF dom a
    -> ASTF dom b
primFunc name f a = inject (PrimFunc name f) :$: a

primFunc2 :: (Typeable a, Typeable b, PrimFunc :<: dom)
    => String
    -> (a -> b -> c)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
primFunc2 name f a b = inject (PrimFunc name f) :$: a :$: b

primFunc3 :: (Typeable a, Typeable b, Typeable c, PrimFunc :<: dom)
    => String
    -> (a -> b -> c -> d)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
primFunc3 name f a b c = inject (PrimFunc name f) :$: a :$: b :$: c

primFunc4 :: (Typeable a, Typeable b, Typeable c, Typeable d, PrimFunc :<: dom)
    => String
    -> (a -> b -> c -> d -> e)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
    -> ASTF dom e
primFunc4 name f a b c d = inject (PrimFunc name f) :$: a :$: b :$: c :$: d

