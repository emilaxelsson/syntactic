-- | Simple symbols
--
-- 'Sym' provides a simple way to make syntactic symbols for prototyping.
-- However, note that 'Sym' is quite unsafe as it only uses 'String' to
-- distinguish between different symbols. Also, 'Sym' has a very free type that
-- allows any number of arguments.

module Language.Syntactic.Features.Symbol where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic



data Sym ctx a
  where
    Sym :: (ConsType a, Sat ctx (EvalResult a)) =>
        String -> ConsEval a -> Sym ctx a

instance WitnessCons (Sym ctx)
  where
    witnessCons (Sym _ _) = ConsWit

instance WitnessSat (Sym ctx)
  where
    type Context (Sym ctx) = ctx
    witnessSat (Sym _ _) = Witness'

witnessSatSym :: forall ctx dom a . (Sym ctx :<: dom)
    => Proxy ctx
    -> ASTF dom a
    -> Maybe (Witness' ctx a)
witnessSatSym ctx = witSym
  where
    witSym :: (EvalResult b ~ a) => AST dom b -> Maybe (Witness' ctx a)
    witSym (prjSym ctx -> Just (Sym _ _)) = Just Witness'
    witSym (f :$: _) = witSym f
    witSym _         = Nothing

instance ExprEq (Sym ctx)
  where
    exprEq (Sym a _) (Sym b _) = a==b
    exprHash (Sym name _)      = hash name

instance Render (Sym ctx)
  where
    renderPart [] (Sym name _) = name
    renderPart args (Sym name _)
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

instance ToTree (Sym ctx)

instance Eval (Sym ctx)
  where
    evaluate (Sym _ a) = fromEval a



-- | A zero-argument symbol
sym0
    :: ( Sat ctx a
       , Sym ctx :<: dom
       )
    => Proxy ctx
    -> String
    -> a
    -> ASTF dom a
sym0 ctx name a = inject (Sym name a `withContext` ctx)

-- | A one-argument symbol
sym1
    :: ( Typeable a
       , Sat ctx b
       , Sym ctx :<: dom
       )
    => Proxy ctx
    -> String
    -> (a -> b)
    -> ASTF dom a
    -> ASTF dom b
sym1 ctx name f a = inject (Sym name f `withContext` ctx) :$: a

-- | A two-argument symbol
sym2
    :: ( Typeable a
       , Typeable b
       , Sat ctx c
       , Sym ctx :<: dom
       )
    => Proxy ctx
    -> String
    -> (a -> b -> c)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
sym2 ctx name f a b = inject (Sym name f `withContext` ctx) :$: a :$: b

-- | A three-argument symbol
sym3
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Sat ctx d
       , Sym ctx :<: dom
       )
    => Proxy ctx
    -> String
    -> (a -> b -> c -> d)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
sym3 ctx name f a b c = inject (Sym name f `withContext` ctx) :$: a :$: b :$: c

-- | A four-argument symbol
sym4
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Typeable d
       , Sat ctx e
       , Sym ctx :<: dom
       )
    => Proxy ctx
    -> String
    -> (a -> b -> c -> d -> e)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
    -> ASTF dom e
sym4 ctx name f a b c d =
    inject (Sym name f `withContext` ctx) :$: a :$: b :$: c :$: d



-- | Partial symbol projection with explicit context
prjSym :: (Sym ctx :<: sup) =>
    Proxy ctx -> sup a -> Maybe (Sym ctx a)
prjSym _ = project



-- | Class of expressions that can be treated as symbols
class IsSymbol expr
  where
    toSym :: expr a -> Sym Poly a

-- | Default implementation of 'exprEq'
exprEqSym :: IsSymbol expr => expr a -> expr b -> Bool
exprEqSym a b = exprEq (toSym a) (toSym b)

-- | Default implementation of 'exprHash'
exprHashSym :: IsSymbol expr => expr a -> Hash
exprHashSym = exprHash . toSym

-- | Default implementation of 'renderPart'
renderPartSym :: IsSymbol expr => [String] -> expr a -> String
renderPartSym args = renderPart args . toSym

-- | Default implementation of 'evaluate'
evaluateSym :: IsSymbol expr => expr a -> a
evaluateSym = evaluate . toSym

