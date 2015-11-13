-- | Construction and elimination of tuples

module Language.Syntactic.Functional.Tuple where



import Language.Syntactic
import Language.Syntactic.Functional



--------------------------------------------------------------------------------
-- * Generic tuple projection
--------------------------------------------------------------------------------

class Select1 tup
  where
    type Sel1 tup
    select1 :: tup -> Sel1 tup

class Select2 tup
  where
    type Sel2 tup
    select2 :: tup -> Sel2 tup

class Select3 tup
  where
    type Sel3 tup
    select3 :: tup -> Sel3 tup

class Select4 tup
  where
    type Sel4 tup
    select4 :: tup -> Sel4 tup

instance Select1 (a,b)
  where
    type Sel1 (a,b) = a
    select1 (a,b) = a

instance Select2 (a,b)
  where
    type Sel2 (a,b) = b
    select2 (a,b) = b

instance Select1 (a,b,c)
  where
    type Sel1 (a,b,c) = a
    select1 (a,b,c) = a

instance Select2 (a,b,c)
  where
    type Sel2 (a,b,c) = b
    select2 (a,b,c) = b

instance Select3 (a,b,c)
  where
    type Sel3 (a,b,c) = c
    select3 (a,b,c) = c

instance Select1 (a,b,c,d)
  where
    type Sel1 (a,b,c,d) = a
    select1 (a,b,c,d) = a

instance Select2 (a,b,c,d)
  where
    type Sel2 (a,b,c,d) = b
    select2 (a,b,c,d) = b

instance Select3 (a,b,c,d)
  where
    type Sel3 (a,b,c,d) = c
    select3 (a,b,c,d) = c

instance Select4 (a,b,c,d)
  where
    type Sel4 (a,b,c,d) = d
    select4 (a,b,c,d) = d



--------------------------------------------------------------------------------
-- * Symbols
--------------------------------------------------------------------------------

-- | Construction and elimination of tuples
data Tuple sig
  where
    Tup2 :: Tuple (a :-> b :-> Full (a,b))
    Tup3 :: Tuple (a :-> b :-> c :-> Full (a,b,c))
    Tup4 :: Tuple (a :-> b :-> c :-> d :-> Full (a,b,c,d))
    Sel1 :: Select1 tup => Tuple (tup :-> Full (Sel1 tup))
    Sel2 :: Select2 tup => Tuple (tup :-> Full (Sel2 tup))
    Sel3 :: Select3 tup => Tuple (tup :-> Full (Sel3 tup))
    Sel4 :: Select4 tup => Tuple (tup :-> Full (Sel4 tup))

instance Symbol Tuple
  where
    symSig Tup2 = signature
    symSig Tup3 = signature
    symSig Tup4 = signature
    symSig Sel1 = signature
    symSig Sel2 = signature
    symSig Sel3 = signature
    symSig Sel4 = signature

instance Render Tuple
  where
    renderSym Tup2 = "tup2"
    renderSym Tup3 = "tup3"
    renderSym Tup4 = "tup4"
    renderSym Sel1 = "sel1"
    renderSym Sel2 = "sel2"
    renderSym Sel3 = "sel3"
    renderSym Sel4 = "sel4"
    renderArgs = renderArgsSmart

instance Equality   Tuple
instance StringTree Tuple

instance Eval Tuple
  where
    evalSym Tup2 = (,)
    evalSym Tup3 = (,,)
    evalSym Tup4 = (,,,)
    evalSym Sel1 = select1
    evalSym Sel2 = select2
    evalSym Sel3 = select3
    evalSym Sel4 = select4

instance EvalEnv Tuple env

