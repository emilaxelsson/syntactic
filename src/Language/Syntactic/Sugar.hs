{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | \"Syntactic sugar\"

module Language.Syntactic.Sugar where



import Language.Syntactic.Syntax
import Language.Syntactic.Constraint



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
    {-# SPECIALIZE instance Syntactic (ASTF dom a) #-}
    type Domain (ASTF dom a)   = dom
    type Internal (ASTF dom a) = a
    desugar = id
    sugar   = id
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}

-- | Syntactic type casting
resugar :: (Syntactic a, Syntactic b, Domain a ~ Domain b, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar
{-# INLINABLE resugar #-}

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
class SyntacticN a internal | a -> internal
  where
    desugarN :: a -> internal
    sugarN   :: internal -> a

instance {-# OVERLAPPABLE #-}
    (Syntactic a, Domain a ~ dom, ia ~ AST dom (Full (Internal a))) => SyntacticN a ia
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , ia ~ AST dom (Full (Internal a))
                            ) => SyntacticN a ia #-}
    desugarN = desugar
    sugarN   = sugar
    {-# INLINABLE desugarN #-}
    {-# INLINABLE sugarN #-}

instance {-# OVERLAPPABLE #-}
    ( Syntactic a
    , Domain a ~ dom
    , ia ~ Internal a
    , SyntacticN b ib
    ) =>
      SyntacticN (a -> b) (AST dom (Full ia) -> ib)
  where
    {-# SPECIALIZE instance ( Syntactic a
                            , Domain a ~ dom
                            , ia ~ Internal a
                            , SyntacticN b ib
                            ) => SyntacticN (a -> b) (AST dom (Full ia) -> ib) #-}
    desugarN f = desugarN . f . sugar
    sugarN f   = sugarN . f . desugar
    {-# INLINABLE desugarN #-}
    {-# INLINABLE sugarN #-}



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
{-# INLINABLE sugarSym #-}

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
{-# INLINABLE sugarSymC #-}
