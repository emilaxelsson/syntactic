-- | Simple symbols
--
-- 'Sym' provides a simple way to make syntactic symbols for prototyping.
-- However, note that 'Sym' is quite unsafe as it only uses 'String' to
-- distinguish between different symbols. Also, 'Sym' has a very free type that
-- allows any number of arguments.

module Language.Syntactic.Features.Symbol where



import Data.Typeable

import Data.Hash

import Language.Syntactic



data Sym a
  where
    Sym :: ConsType a => String -> ConsEval a -> Sym a

instance WitnessCons Sym
  where
    witnessCons (Sym _ _) = ConsWit

instance ExprEq Sym
  where
    exprEq (Sym a _) (Sym b _) = a==b
    exprHash (Sym name _)      = hash name

instance Render Sym
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

instance ToTree Sym

instance Eval Sym
  where
    evaluate (Sym _ a) = fromEval a



-- | A zero-argument symbol
sym0
    :: ( Typeable a
       , Sym :<: dom
       )
    => String
    -> a
    -> ASTF dom a
sym0 name a = inject (Sym name a)

-- | A one-argument symbol
sym1
    :: ( Typeable a
       , Sym :<: dom
       )
    => String
    -> (a -> b)
    -> ASTF dom a
    -> ASTF dom b
sym1 name f a = inject (Sym name f) :$: a

-- | A two-argument symbol
sym2
    :: ( Typeable a
       , Typeable b
       , Sym :<: dom
       )
    => String
    -> (a -> b -> c)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
sym2 name f a b = inject (Sym name f) :$: a :$: b

-- | A three-argument symbol
sym3
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Sym :<: dom
       )
    => String
    -> (a -> b -> c -> d)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
sym3 name f a b c = inject (Sym name f) :$: a :$: b :$: c

-- | A four-argument symbol
sym4
    :: ( Typeable a
       , Typeable b
       , Typeable c
       , Typeable d
       , Sym :<: dom
       )
    => String
    -> (a -> b -> c -> d -> e)
    -> ASTF dom a
    -> ASTF dom b
    -> ASTF dom c
    -> ASTF dom d
    -> ASTF dom e
sym4 name f a b c d = inject (Sym name f) :$: a :$: b :$: c :$: d



-- | Class of expressions that can be treated as symbols
class IsSymbol expr
  where
    toSym :: expr a -> Sym a

-- | Default implementation of 'exprEq'
exprEqFunc :: IsSymbol expr => expr a -> expr b -> Bool
exprEqFunc a b = exprEq (toSym a) (toSym b)

-- | Default implementation of 'exprHash'
exprHashFunc :: IsSymbol expr => expr a -> Hash
exprHashFunc = exprHash . toSym

-- | Default implementation of 'renderPart'
renderPartFunc :: IsSymbol expr => [String] -> expr a -> String
renderPartFunc args = renderPart args . toSym

-- | Default implementation of 'evaluate'
evaluateFunc :: IsSymbol expr => expr a -> a
evaluateFunc = evaluate . toSym

