{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

import Language.Syntactic



----------------------------------------
-- a)
----------------------------------------

data Circ a
  where
    Const :: Bool -> Circ Bool
    Inv   :: Circ Bool -> Circ Bool
    And   :: Circ Bool -> Circ Bool -> Circ Bool

data ConstSym a where Const' :: Bool -> ConstSym (Full Bool)
data InvSym a   where Inv' :: InvSym (Bool :-> Full Bool)
data AndSym a   where And' :: AndSym (Bool :-> Bool :-> Full Bool)

type CircDom = InvSym :+: AndSym :+: ConstSym



----------------------------------------
-- b)
----------------------------------------

consT :: (ConstSym :<: dom) => Bool -> ASTF dom Bool
consT a = inject (Const' a)

inv :: (InvSym :<: dom) => ASTF dom Bool -> ASTF dom Bool
inv a = inject Inv' :$: a

anD :: (AndSym :<: dom) =>
    ASTF dom Bool -> ASTF dom Bool -> ASTF dom Bool
anD a b = inject And' :$: a :$: b



----------------------------------------
-- c)
----------------------------------------

circ1 :: Circ Bool
circ1 = And (Const False) (And (Const True) (Inv (Const False)))

circ2 :: ASTF CircDom Bool
circ2 = anD (consT False) (anD (consT True) (inv (consT False)))



----------------------------------------
-- d)
----------------------------------------

fromCirc :: Circ a -> ASTF CircDom a
fromCirc (Const a) = inject (Const' a)
fromCirc (Inv a)   = inject Inv' :$: fromCirc a
fromCirc (And a b) = inject And' :$: fromCirc a :$: fromCirc b

toCirc :: ASTF CircDom a -> Circ a
toCirc (project -> Just (Const' a))         = Const a
toCirc ((project -> Just Inv') :$: a)       = Inv (toCirc a)
toCirc ((project -> Just And') :$: a :$: b) = And (toCirc a) (toCirc b)



----------------------------------------
-- e)
----------------------------------------

instance Render ConstSym where render (Const' a) = show a
instance Render InvSym   where render Inv' = "inv"
instance Render AndSym   where render And' = "and"

instance Eval ConstSym where evaluate (Const' a) = fromEval a
instance Eval InvSym   where evaluate Inv' = fromEval not
instance Eval AndSym   where evaluate And' = fromEval (&&)



----------------------------------------
-- f)
----------------------------------------

data NandSym a where Nand :: NandSym (Bool :-> Bool :-> Full Bool)

instance Render NandSym where render Nand = "nand"

instance Eval NandSym where evaluate Nand = fromEval $ \a b -> not (a && b)

nandify' :: AST (InvSym :+: AndSym :+: dom) a -> AST (NandSym :+: dom) a
nandify' ((project -> Just Inv') :$: a) = inject Nand :$: a' :$: a'
  where
    a' = nandify a
nandify' ((project -> Just And') :$: a :$: b) = inject Nand :$: ab :$: ab
  where
    ab = inject Nand :$: nandify a :$: nandify b
nandify' (c :$: a) = nandify' c :$: nandify a
nandify' (Symbol (InjectR (InjectR a))) = Symbol (InjectR a)

nandify ::
    ASTF (InvSym :+: AndSym :+: dom) a -> ASTF (NandSym :+: dom) a
nandify = nandify'

