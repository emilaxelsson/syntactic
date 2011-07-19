-- | Construction and projection of tuples in the object language
--
-- The function pairs @desugarTupX@/@sugarTupX@ could be used directly in
-- 'Syntactic' instances if it wasn't for the extra @(`Proxy` ctx)@ arguments.
-- For this reason, 'Syntactic' instances have to be written manually for each
-- context. The module "Language.Syntactic.Features.TupleSyntacticPoly" provides
-- instances for a 'Poly' context. The exact same code can be used to make
-- instances for other contexts -- just copy/paste and replace 'Poly' and 'poly'
-- with the desired context (and probably add an extra constraint in the class
-- contexts).

module Language.Syntactic.Features.Tuple where



import Data.Hash
import Data.Proxy
import Data.Tuple.Select

import Language.Syntactic
import Language.Syntactic.Features.PrimFunc



--------------------------------------------------------------------------------
-- * Construction
--------------------------------------------------------------------------------

-- | Expressions for constructing tuples
data Tuple ctx a
  where
    Tup2 :: Sat ctx (a,b)           => Tuple ctx (a :-> b :-> Full (a,b))
    Tup3 :: Sat ctx (a,b,c)         => Tuple ctx (a :-> b :-> c :-> Full (a,b,c))
    Tup4 :: Sat ctx (a,b,c,d)       => Tuple ctx (a :-> b :-> c :-> d :-> Full (a,b,c,d))
    Tup5 :: Sat ctx (a,b,c,d,e)     => Tuple ctx (a :-> b :-> c :-> d :-> e :-> Full (a,b,c,d,e))
    Tup6 :: Sat ctx (a,b,c,d,e,f)   => Tuple ctx (a :-> b :-> c :-> d :-> e :-> f :-> Full (a,b,c,d,e,f))
    Tup7 :: Sat ctx (a,b,c,d,e,f,g) => Tuple ctx (a :-> b :-> c :-> d :-> e :-> f :-> g :-> Full (a,b,c,d,e,f,g))

instance WitnessCons (Tuple ctx)
  where
    witnessCons Tup2 = ConsWit
    witnessCons Tup3 = ConsWit
    witnessCons Tup4 = ConsWit
    witnessCons Tup5 = ConsWit
    witnessCons Tup6 = ConsWit
    witnessCons Tup7 = ConsWit

instance WitnessSat (Tuple ctx)
  where
    type Context (Tuple ctx) = ctx
    witnessSat Tup2 = witness
    witnessSat Tup3 = witness
    witnessSat Tup4 = witness
    witnessSat Tup5 = witness
    witnessSat Tup6 = witness
    witnessSat Tup7 = witness

instance IsFunction (Tuple ctx)
  where
    toFunction Tup2 = PrimFunc "tup2" (,)
    toFunction Tup3 = PrimFunc "tup3" (,,)
    toFunction Tup4 = PrimFunc "tup4" (,,,)
    toFunction Tup5 = PrimFunc "tup5" (,,,,)
    toFunction Tup6 = PrimFunc "tup6" (,,,,,)
    toFunction Tup7 = PrimFunc "tup7" (,,,,,,)

instance ExprEq   (Tuple ctx) where exprEq     = exprEqFunc
instance Render   (Tuple ctx) where renderPart = renderPartFunc
instance Eval     (Tuple ctx) where evaluate   = evaluateFunc
instance ExprHash (Tuple ctx) where exprHash   = exprHashFunc
instance ToTree   (Tuple ctx)

-- | Partial `Tuple` projection with explicit context
prjTuple :: (Tuple ctx :<: sup) => Proxy ctx -> sup a -> Maybe (Tuple ctx a)
prjTuple _ = project



desugarTup2
    :: ( Syntactic a dom
       , Syntactic b dom
       , Sat ctx (Internal a, Internal b)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b)
    -> ASTF dom (Internal a, Internal b)
desugarTup2 ctx (a,b) = inject (Tup2 `withContext` ctx)
    :$: desugar a
    :$: desugar b

desugarTup3
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Sat ctx (Internal a, Internal b, Internal c)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b,c)
    -> ASTF dom (Internal a, Internal b, Internal c)
desugarTup3 ctx (a,b,c) = inject (Tup3 `withContext` ctx)
    :$: desugar a
    :$: desugar b
    :$: desugar c

desugarTup4
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Sat ctx (Internal a, Internal b, Internal c, Internal d)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b,c,d)
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d)
desugarTup4 ctx (a,b,c,d) = inject (Tup4 `withContext` ctx)
    :$: desugar a
    :$: desugar b
    :$: desugar c
    :$: desugar d

desugarTup5
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Sat ctx (Internal a, Internal b, Internal c, Internal d, Internal e)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b,c,d,e)
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e)
desugarTup5 ctx (a,b,c,d,e) = inject (Tup5 `withContext` ctx)
    :$: desugar a
    :$: desugar b
    :$: desugar c
    :$: desugar d
    :$: desugar e

desugarTup6
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Syntactic f dom
       , Sat ctx (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b,c,d,e,f)
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f)
desugarTup6 ctx (a,b,c,d,e,f) = inject (Tup6 `withContext` ctx)
    :$: desugar a
    :$: desugar b
    :$: desugar c
    :$: desugar d
    :$: desugar e
    :$: desugar f

desugarTup7
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Syntactic f dom
       , Syntactic g dom
       , Sat ctx (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f, Internal g)
       , Tuple ctx :<: dom
       )
    => Proxy ctx
    -> (a,b,c,d,e,f,g)
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f, Internal g)
desugarTup7 ctx (a,b,c,d,e,f,g) = inject (Tup7 `withContext` ctx)
    :$: desugar a
    :$: desugar b
    :$: desugar c
    :$: desugar d
    :$: desugar e
    :$: desugar f
    :$: desugar g



--------------------------------------------------------------------------------
-- * Projection
--------------------------------------------------------------------------------

-- | Expressions for selecting elements of a tuple
data Select ctx a
  where
    Sel1 :: (Sel1 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel2 :: (Sel2 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel3 :: (Sel3 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel4 :: (Sel4 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel5 :: (Sel5 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel6 :: (Sel6 a b, Sat ctx b) => Select ctx (a :-> Full b)
    Sel7 :: (Sel7 a b, Sat ctx b) => Select ctx (a :-> Full b)

instance WitnessCons (Select ctx)
  where
    witnessCons Sel1 = ConsWit
    witnessCons Sel2 = ConsWit
    witnessCons Sel3 = ConsWit
    witnessCons Sel4 = ConsWit
    witnessCons Sel5 = ConsWit
    witnessCons Sel6 = ConsWit
    witnessCons Sel7 = ConsWit

instance WitnessSat (Select ctx)
  where
    type Context (Select ctx) = ctx
    witnessSat Sel1 = witness
    witnessSat Sel2 = witness
    witnessSat Sel3 = witness
    witnessSat Sel4 = witness
    witnessSat Sel5 = witness
    witnessSat Sel6 = witness
    witnessSat Sel7 = witness

instance IsFunction (Select ctx)
  where
    toFunction Sel1 = PrimFunc "sel1" sel1
    toFunction Sel2 = PrimFunc "sel2" sel2
    toFunction Sel3 = PrimFunc "sel3" sel3
    toFunction Sel4 = PrimFunc "sel4" sel4
    toFunction Sel5 = PrimFunc "sel5" sel5
    toFunction Sel6 = PrimFunc "sel6" sel6
    toFunction Sel7 = PrimFunc "sel7" sel7

instance ExprEq   (Select ctx) where exprEq     = exprEqFunc
instance Render   (Select ctx) where renderPart = renderPartFunc
instance Eval     (Select ctx) where evaluate   = evaluateFunc
instance ExprHash (Select ctx) where exprHash   = exprHashFunc
instance ToTree   (Select ctx)

-- | Partial `Select` projection with explicit context
prjSelect :: (Select ctx :<: sup) => Proxy ctx -> sup a -> Maybe (Select ctx a)
prjSelect _ = project

-- | Return the selected position, e.g.
--
-- > selectPos (Sel3 poly :: Select Poly ((Int,Int,Int,Int) :-> Full Int)) = 3
selectPos :: Select ctx a -> Int
selectPos Sel1 = 1
selectPos Sel2 = 2
selectPos Sel3 = 3
selectPos Sel4 = 4
selectPos Sel5 = 5
selectPos Sel6 = 6
selectPos Sel7 = 7



sugarTup2
    :: ( Syntactic a dom
       , Syntactic b dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b)
    -> (a,b)
sugarTup2 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    )

sugarTup3
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Sat ctx (Internal c)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b, Internal c)
    -> (a,b,c)
sugarTup3 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    , sugar $ inject (Sel3 `withContext` ctx) :$: a
    )

sugarTup4
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Sat ctx (Internal c)
       , Sat ctx (Internal d)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d)
    -> (a,b,c,d)
sugarTup4 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    , sugar $ inject (Sel3 `withContext` ctx) :$: a
    , sugar $ inject (Sel4 `withContext` ctx) :$: a
    )

sugarTup5
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Sat ctx (Internal c)
       , Sat ctx (Internal d)
       , Sat ctx (Internal e)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e)
    -> (a,b,c,d,e)
sugarTup5 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    , sugar $ inject (Sel3 `withContext` ctx) :$: a
    , sugar $ inject (Sel4 `withContext` ctx) :$: a
    , sugar $ inject (Sel5 `withContext` ctx) :$: a
    )

sugarTup6
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Syntactic f dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Sat ctx (Internal c)
       , Sat ctx (Internal d)
       , Sat ctx (Internal e)
       , Sat ctx (Internal f)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f)
    -> (a,b,c,d,e,f)
sugarTup6 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    , sugar $ inject (Sel3 `withContext` ctx) :$: a
    , sugar $ inject (Sel4 `withContext` ctx) :$: a
    , sugar $ inject (Sel5 `withContext` ctx) :$: a
    , sugar $ inject (Sel6 `withContext` ctx) :$: a
    )

sugarTup7
    :: ( Syntactic a dom
       , Syntactic b dom
       , Syntactic c dom
       , Syntactic d dom
       , Syntactic e dom
       , Syntactic f dom
       , Syntactic g dom
       , Sat ctx (Internal a)
       , Sat ctx (Internal b)
       , Sat ctx (Internal c)
       , Sat ctx (Internal d)
       , Sat ctx (Internal e)
       , Sat ctx (Internal f)
       , Sat ctx (Internal g)
       , Select ctx :<: dom
       )
    => Proxy ctx
    -> ASTF dom (Internal a, Internal b, Internal c, Internal d, Internal e, Internal f, Internal g)
    -> (a,b,c,d,e,f,g)
sugarTup7 ctx a =
    ( sugar $ inject (Sel1 `withContext` ctx) :$: a
    , sugar $ inject (Sel2 `withContext` ctx) :$: a
    , sugar $ inject (Sel3 `withContext` ctx) :$: a
    , sugar $ inject (Sel4 `withContext` ctx) :$: a
    , sugar $ inject (Sel5 `withContext` ctx) :$: a
    , sugar $ inject (Sel6 `withContext` ctx) :$: a
    , sugar $ inject (Sel7 `withContext` ctx) :$: a
    )

