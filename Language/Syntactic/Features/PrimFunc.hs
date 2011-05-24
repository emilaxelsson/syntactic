-- | Primitive functions

module Language.Syntactic.Features.PrimFunc where



import Data.Typeable

import Data.Hash

import Language.Syntactic



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
    evaluate (PrimFunc _ f) = fromEval f

instance ExprHash PrimFunc
  where
    exprHash (PrimFunc name _) = hash name



primFunc1
    :: ( Typeable a
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b)
    -> ASTF dom a
    -> ASTF dom b
primFunc1 name f a = inject (PrimFunc name f) :$: a

primFunc2
    :: ( Typeable a
       , Typeable b
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
primFunc2 name f a b = inject (PrimFunc name f) :$: a :$: b

primFunc3
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c -> d)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
primFunc3 name f a b c = inject (PrimFunc name f) :$: a :$: b :$: c

primFunc4
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Typeable d
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c -> d -> e)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
    -> ASTF dom e
primFunc4 name f a b c d = inject (PrimFunc name f) :$: a :$: b :$: c :$: d

primFuncAnn1
    :: ( Typeable a
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b)
    -> info b
    -> AnnSTF info dom a
    -> AnnSTF info dom b
primFuncAnn1 name f ib a = injectAnn ib (PrimFunc name f) :$: a

primFuncAnn2
    :: ( Typeable a
       , Typeable b
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c)
    -> info c
    -> AnnSTF info dom a
    -> AnnSTF info dom b
    -> AnnSTF info dom c
primFuncAnn2 name f ic a b = injectAnn ic (PrimFunc name f) :$: a :$: b

primFuncAnn3
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c -> d)
    -> info d
    -> AnnSTF info dom a
    -> AnnSTF info dom b
    -> AnnSTF info dom c
    -> AnnSTF info dom d
primFuncAnn3 name f id a b c =
    injectAnn id (PrimFunc name f) :$: a :$: b :$: c

primFuncAnn4
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Typeable d
       , PrimFunc :<: dom
       )
    => String
    -> (a -> b -> c -> d -> e)
    -> info e
    -> AnnSTF info dom a
    -> AnnSTF info dom b
    -> AnnSTF info dom c
    -> AnnSTF info dom d
    -> AnnSTF info dom e
primFuncAnn4 name f ie a b c d =
    injectAnn ie (PrimFunc name f) :$: a :$: b :$: c :$: d



-- | Class of expressions that can be treated as primitive functions
class IsFunction expr
  where
    toFunction :: expr a -> PrimFunc a

-- | Default implementation of 'exprEq'
exprEqFunc :: IsFunction expr => expr a -> expr b -> Bool
exprEqFunc a b = exprEq (toFunction a) (toFunction b)

-- | Default implementation of 'renderPart'
renderPartFunc :: IsFunction expr => [String] -> expr a -> String
renderPartFunc args = renderPart args . toFunction

-- | Default implementation of 'evaluate'
evaluateFunc :: IsFunction expr => expr a -> a
evaluateFunc = evaluate . toFunction

-- | Default implementation of 'exprHash'
exprHashFunc :: IsFunction expr => expr a -> Hash
exprHashFunc = exprHash . toFunction

