{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | \"Syntactic sugar\"

module Language.Syntactic.Sugar where



import Language.Syntactic.Syntax
import Language.Syntactic.Constraint



-- | It is usually assumed that @(`desugar` (`sugar` a))@ has the same meaning
-- as @a@.
class (Constrained dom, Sat dom (Internal a)) => Syntactic a dom | a -> dom
    -- Note: using a functional dependency rather than an associated type,
    -- because this makes it possible to make a class alias constraining dom.
    -- TODO Now that GHC allows equality super class constraints, this should be
    --      changed to an associated type.
  where
    type Internal a
    desugar :: a -> ASTF dom (Internal a)
    sugar   :: ASTF dom (Internal a) -> a

instance (Constrained dom, Sat dom a) => Syntactic (ASTF dom a) dom
  where
    type Internal (ASTF dom a) = a
    desugar = id
    sugar   = id

-- | Syntactic type casting
resugar :: (Syntactic a dom, Syntactic b dom, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar

-- | N-ary syntactic functions
--
-- 'desugarN' has any type of the form:
--
-- > desugarN ::
-- >     ( Syntactic a dom
-- >     , Syntactic b dom
-- >     , ...
-- >     , Syntactic x dom
-- >     ) => (a -> b -> ... -> x)
-- >       -> (  ASTF dom (Internal a)
-- >          -> ASTF dom (Internal b)
-- >          -> ...
-- >          -> ASTF dom (Internal x)
-- >          )
--
-- ...and vice versa for 'sugarN'.
class SyntacticN a internal | a -> internal
  where
    desugarN :: a -> internal
    sugarN   :: internal -> a

instance (Syntactic a dom, ia ~ AST dom (Full (Internal a))) => SyntacticN a ia
  where
    desugarN = desugar
    sugarN   = sugar

instance
    ( Syntactic a dom
    , ia ~ Internal a
    , SyntacticN b ib
    ) =>
      SyntacticN (a -> b) (AST dom (Full ia) -> ib)
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
sugarSym :: (sym :<: AST dom, ApplySym sig b dom, SyntacticN c b) =>
    sym sig -> c
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
       , ApplySym sig b dom
       , SyntacticN c b
       )
    => sym sig -> c
sugarSymC = sugarN . appSymC

