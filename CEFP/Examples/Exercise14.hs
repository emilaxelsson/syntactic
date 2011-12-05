{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Option where



import Language.Syntactic

import MuFeldspar.Core
import MuFeldspar.Frontend



data Option a = Option { isSome :: Data Bool, fromSome :: a }

instance Syntax a => Syntactic (Option a) FeldDomainAll
  where
    type Internal (Option a) = (Bool, Internal a)
    desugar = desugar . freezeOption . fmap resugar
    sugar   = fmap resugar . unfreezeOption . sugar

instance Functor Option
  where
    fmap f opt = opt {fromSome = f (fromSome opt)}

instance Monad Option
  where
    return = some
    a >>= f = b { isSome = isSome a ? (isSome b, false) }
      where
        b = f (fromSome a)



freezeOption :: Type a => Option (Data a) -> Data (Bool,a)
freezeOption a = resugar (isSome a, fromSome a)

unfreezeOption :: Type a => Data (Bool,a) -> Option (Data a)
unfreezeOption (resugar -> (valid,a)) = Option valid a

undef :: Syntax a => a
undef = resugar $ getIx (value []) 0

some :: a -> Option a
some = Option true

none :: Syntax a => Option a
none = Option false undef

option :: Syntax b => b -> (a -> b) -> Option a -> b
option noneCase someCase opt = isSome opt ?
    ( someCase (fromSome opt)
    , noneCase
    )

oplus :: Syntax a => Option a -> Option a -> Option a
oplus a b = isSome a ? (a,b)

