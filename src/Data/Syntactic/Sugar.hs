{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | \"Syntactic sugar\"
--
-- For details, see "Combining Deep and Shallow Embedding for EDSL"
-- (TFP 2013, <http://www.cse.chalmers.se/~emax/documents/svenningsson2013combining.pdf>).

module Data.Syntactic.Sugar where



import Data.Syntactic.Syntax



-- | It is usually assumed that @(`desugar` (`sugar` a))@ has the same meaning
-- as @a@.
class Syntactic a
  where
    type Domain a :: * -> *
    type Internal a
    desugar :: a -> ASTF (Domain a) (Internal a)
    sugar   :: ASTF (Domain a) (Internal a) -> a

instance Syntactic (ASTF sym a)
  where
    type Domain (ASTF sym a)   = sym
    type Internal (ASTF sym a) = a
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
-- >     , Domain a ~ sym
-- >     , Domain b ~ sym
-- >     , ...
-- >     , Domain x ~ sym
-- >     ) => (a -> b -> ... -> x)
-- >       -> (  ASTF sym (Internal a)
-- >          -> ASTF sym (Internal b)
-- >          -> ...
-- >          -> ASTF sym (Internal x)
-- >          )
--
-- ...and vice versa for 'sugarN'.
class SyntacticN f internal | f -> internal
  where
    desugarN :: f -> internal
    sugarN   :: internal -> f

instance {-# OVERLAPPING #-}
         (Syntactic f, Domain f ~ sym, fi ~ AST sym (Full (Internal f))) => SyntacticN f fi
  where
    desugarN = desugar
    sugarN   = sugar

instance {-# OVERLAPPING #-}
    ( Syntactic a
    , Domain a ~ sym
    , ia ~ Internal a
    , SyntacticN f fi
    ) =>
      SyntacticN (a -> f) (AST sym (Full ia) -> fi)
  where
    desugarN f = desugarN . f . sugar
    sugarN f   = sugarN . f . desugar

-- | \"Sugared\" symbol application
--
-- 'sugarSym' has any type of the form:
--
-- > sugarSym ::
-- >     ( sub :<: AST sup
-- >     , Syntactic a
-- >     , Syntactic b
-- >     , ...
-- >     , Syntactic x
-- >     , Domain a ~ Domain b ~ ... ~ Domain x
-- >     ) => sub (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >       -> (a -> b -> ... -> x)
sugarSym
    :: ( Signature sig
       , fi  ~ SmartFun sup sig
       , sig ~ SmartSig fi
       , sup ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: sup
       )
    => sub sig -> f
sugarSym = sugarN . smartSym

