{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | \"Syntactic sugar\"
--
-- For details, see: Combining Deep and Shallow Embedding for EDSL
-- (TFP 2013, <http://www.cse.chalmers.se/~emax/documents/svenningsson2013combining.pdf>).

module Data.Syntactic.Sugar where



import Data.Syntactic.Syntax
import Data.Syntactic.Constraint



-- | It is usually assumed that @(`desugar` (`sugar` a))@ has the same meaning
-- as @a@.
class Syntactic a
  where
    type Domain a :: * -> *
    type Internal a
    desugar :: a -> ASTF (Domain a) (Internal a)
    sugar   :: ASTF (Domain a) (Internal a) -> a

instance Syntactic (ASTF dom a)
  where
    type Domain (ASTF dom a)   = dom
    type Internal (ASTF dom a) = a
    desugar = id
    sugar   = id

-- | Syntactic type casting
resugar :: (Syntactic a, Syntactic b, Domain a ~ Domain b, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar

-- | N-ary syntactic functions
--
-- 'desugarN' has any type of the form:
--
-- > desugarN ::
-- >     ( Syntactic a
-- >     , Syntactic b
-- >     , ...
-- >     , Syntactic x
-- >     , Domain a ~ dom
-- >     , Domain b ~ dom
-- >     , ...
-- >     , Domain x ~ dom
-- >     ) => (a -> b -> ... -> x)
-- >       -> (  ASTF dom (Internal a)
-- >          -> ASTF dom (Internal b)
-- >          -> ...
-- >          -> ASTF dom (Internal x)
-- >          )
--
-- ...and vice versa for 'sugarN'.
class SyntacticN f internal | f -> internal
  where
    desugarN :: f -> internal
    sugarN   :: internal -> f

instance (Syntactic f, Domain f ~ dom, fi ~ AST dom (Full (Internal f))) => SyntacticN f fi
  where
    desugarN = desugar
    sugarN   = sugar

instance
    ( Syntactic a
    , Domain a ~ dom
    , ia ~ Internal a
    , SyntacticN f fi
    ) =>
      SyntacticN (a -> f) (AST dom (Full ia) -> fi)
  where
    desugarN f = desugarN . f . sugar
    sugarN f   = sugarN . f . desugar



-- | \"Sugared\" symbol application
--
-- 'sugarSym' has any type of the form:
--
-- > sugarSym ::
-- >     ( expr :<: AST dom
-- >     , Syntactic a dom
-- >     , Syntactic b dom
-- >     , ...
-- >     , Syntactic x dom
-- >     ) => expr (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >       -> (a -> b -> ... -> x)
sugarSym :: (sym :<: AST dom, ApplySym sig fi dom, SyntacticN f fi) => sym sig -> f
sugarSym = sugarN . appSym

-- | \"Sugared\" symbol application
--
-- 'sugarSymC' has any type of the form:
--
-- > sugarSymC ::
-- >     ( InjectC expr (AST dom) (Internal x)
-- >     , Syntactic a dom
-- >     , Syntactic b dom
-- >     , ...
-- >     , Syntactic x dom
-- >     ) => expr (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >       -> (a -> b -> ... -> x)
sugarSymC
    :: ( InjectC sym (AST dom) (DenResult sig)
       , ApplySym sig fi dom
       , SyntacticN f fi
       )
    => sym sig -> f
sugarSymC = sugarN . appSymC

