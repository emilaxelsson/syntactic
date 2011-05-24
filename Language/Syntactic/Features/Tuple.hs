-- | Construction and selection of tuples

module Language.Syntactic.Features.Tuple where



import Data.Hash
import Data.Tuple.Select

import Language.Syntactic
import Language.Syntactic.Features.PrimFunc



-- | Expressions for constructing tuples
data Tuple a
  where
    Tup2 :: Tuple (a :-> b :-> Full (a,b))
    Tup3 :: Tuple (a :-> b :-> c :-> Full (a,b,c))
    Tup4 :: Tuple (a :-> b :-> c :-> d :-> Full (a,b,c,d))
    Tup5 :: Tuple (a :-> b :-> c :-> d :-> e :-> Full (a,b,c,d,e))
    Tup6 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> Full (a,b,c,d,e,f))
    Tup7 :: Tuple (a :-> b :-> c :-> d :-> e :-> f :-> g :-> Full (a,b,c,d,e,f,g))

instance IsFunction Tuple
  where
    toFunction Tup2 = PrimFunc "tup2" (,)
    toFunction Tup3 = PrimFunc "tup3" (,,)
    toFunction Tup4 = PrimFunc "tup4" (,,,)
    toFunction Tup5 = PrimFunc "tup5" (,,,,)
    toFunction Tup6 = PrimFunc "tup6" (,,,,,)
    toFunction Tup7 = PrimFunc "tup7" (,,,,,,)

instance ExprEq   Tuple where exprEq     = exprEqFunc
instance Render   Tuple where renderPart = renderPartFunc
instance Eval     Tuple where evaluate   = evaluateFunc
instance ExprHash Tuple where exprHash   = exprHashFunc
instance ToTree   Tuple

-- | Expressions for selecting elements of a tuple
data Select a
  where
    Sel1 :: Sel1 a b => Select (a :-> Full b)
    Sel2 :: Sel2 a b => Select (a :-> Full b)
    Sel3 :: Sel3 a b => Select (a :-> Full b)
    Sel4 :: Sel4 a b => Select (a :-> Full b)
    Sel5 :: Sel5 a b => Select (a :-> Full b)
    Sel6 :: Sel6 a b => Select (a :-> Full b)
    Sel7 :: Sel7 a b => Select (a :-> Full b)

instance IsFunction Select
  where
    toFunction Sel1 = PrimFunc "sel1" sel1
    toFunction Sel2 = PrimFunc "sel2" sel2
    toFunction Sel3 = PrimFunc "sel3" sel3
    toFunction Sel4 = PrimFunc "sel4" sel4
    toFunction Sel5 = PrimFunc "sel5" sel5
    toFunction Sel6 = PrimFunc "sel6" sel6
    toFunction Sel7 = PrimFunc "sel7" sel7

instance ExprEq   Select where exprEq     = exprEqFunc
instance Render   Select where renderPart = renderPartFunc
instance Eval     Select where evaluate   = evaluateFunc
instance ExprHash Select where exprHash   = exprHashFunc
instance ToTree   Select

-- | Return the selected position, e.g.
--
-- > selectPos (Sel3 :: Select ((Int,Int,Int,Int) -> Int)) = 3
selectPos :: Select a -> Int
selectPos Sel1 = 1
selectPos Sel2 = 2
selectPos Sel3 = 3
selectPos Sel4 = 4
selectPos Sel5 = 5
selectPos Sel6 = 6
selectPos Sel7 = 7

