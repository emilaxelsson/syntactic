module Normal (main) where

import Criterion.Main
import Criterion.Types
import Language.Syntactic
import Language.Syntactic.Functional

main :: IO ()
main = defaultMainWith (defaultConfig {csvFile = Just "bench-results/normal.csv"})
         [ bgroup "Eval Tree 10"   [ bench "gadt"      $ nf evl (gadtExpr 10)
                                   , bench "syntactic" $ nf evalDen (syntacticExpr 10)]
         , bgroup "Eval Tree 15"   [ bench "gadt"      $ nf evl (gadtExpr 15)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 15)]
         , bgroup "Eval Tree 20"   [ bench "gadt"      $ nf evl (gadtExpr 20)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 20) ]
         , bgroup "Size Tree 10"   [ bench "gadt"      $ nf gSize (gadtExpr 10)
                                   , bench "syntactic" $ nf size (syntacticExpr 10)]
         , bgroup "Size Tree 15"   [ bench "gadt"      $ nf gSize (gadtExpr 15)
                                   , bench "syntactic" $ nf size (syntacticExpr 15)]
         , bgroup "Size Tree 20"   [ bench "gadt"      $ nf gSize (gadtExpr 20)
                                   , bench "syntactic" $ nf size (syntacticExpr 20)]
         , bgroup "Eval IFTree 10" [ bench "if gadt"   $ nf evl (gadtExpr 10)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 10)]
         , bgroup "Eval IFTree 15" [ bench "gadt"      $ nf evl (gadtExpr 15)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 15)]
         , bgroup "Eval IFTree 20" [ bench "gadt"      $ nf evl (gadtExpr 20)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 20) ]
         , bgroup "Size IFTree 10" [ bench "gadt"      $ nf gSize (gadtExpr 10)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 10)]
         , bgroup "Size IFTree 15" [ bench "gadt"      $ nf gSize (gadtExpr 15)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 15)]
         , bgroup "Size IFTree 20" [ bench "gadt"      $ nf gSize (gadtExpr 20)
                                   , bench "syntactic" $ nf evalDen(syntacticExpr 20) ]]

-- Expressions
gadtExpr :: Int -> Expr Int
gadtExpr 0 = (If ((LitI 5) :== (LitI 4)) (LitI 5) (LitI 0))
gadtExpr n = gadtExpr (n-1) :+ gadtExpr (n-1)

gadtExprIf :: Int -> Expr Int
gadtExprIf 0 = (If ((LitI 5) :== (LitI 4)) (LitI 5) (LitI 0))
gadtExprIf n = (If (gadtExprIf (n-1) :== (LitI 0)) (gadtExprIf (n-1)) (gadtExprIf (n-1)))

syntacticExpr :: Int -> ExprS' Int
syntacticExpr 0 = if' (eq (int 5) (int 4)) (int 5) (int 0)
syntacticExpr n = (add (syntacticExpr (n-1)) (syntacticExpr (n-1)))

-- We also test an expression with several ifs so the tree has higher width.
syntacticExprIf :: Int -> ExprS' Int
syntacticExprIf 0 = if' (eq (int 5) (int 4)) (int 5) (int 0)
syntacticExprIf n = if' (eq (syntacticExprIf(n-1)) (int 0)) (syntacticExprIf (n-1)) (syntacticExprIf (n-1))


-- Comparing Syntactic with GADTs
-- GADTs
data Expr t where
  LitI  :: Int                           -> Expr Int
  LitB  :: Bool                          -> Expr Bool
  (:+)  ::         Expr Int -> Expr Int  -> Expr Int
  (:==) :: Eq t => Expr t   -> Expr t    -> Expr Bool
  If    :: Expr Bool -> Expr t -> Expr t -> Expr t

evl :: Expr t -> t
evl (LitI n)     =  n
evl (LitB b)     =  b
evl (e1 :+ e2)   =  evl e1 +  evl e2
evl (e1 :== e2)  =  evl e1 == evl e2
evl (If b t e)   =  if evl b then evl t else evl e

gSize :: Expr t ->  Int
gSize (LitI n)     =  1
gSize (LitB b)     =  1
gSize (e1 :+ e2)   =  gSize e1 +  gSize e2
gSize (e1 :== e2)  =  gSize e1 + gSize e2
gSize (If b t e)   =  gSize b + gSize t +  gSize e

-- Syntactic

data ExprS t where
  EI    :: Int  -> ExprS (Full Int)
  EB    :: Bool -> ExprS (Full Bool)
  EAdd  :: ExprS (Int :-> Int :-> Full Int)
  EEq   :: (Eq t) => ExprS (t   :-> t   :-> Full Bool)
  EIf   :: ExprS (Bool :-> a :-> a :-> Full a)

type ExprS' a = AST ExprS (Full a)

-- Smart constructors
int  :: Int -> ExprS' Int
int = Sym . EI

bool :: Bool -> ExprS' Bool
bool = Sym . EB

add  :: ExprS' Int -> ExprS' Int -> ExprS' Int
add a b = Sym EAdd :$ a :$ b

eq   :: (Eq a) => ExprS' a -> ExprS' a -> ExprS' Bool
eq a b = Sym EEq :$ a :$ b

if'  :: ExprS' Bool -> ExprS' a -> ExprS' a -> ExprS' a
if' c a b = Sym EIf :$ c :$ a :$ b

instance Render ExprS where
  renderSym (EI n) = "EI"
  renderSym (EB b) = "EB"
  renderSym EAdd   = "EAdd"
  renderSym EEq    = "EEq"
  renderSym EIf    = "EIf"

instance Equality   ExprS
instance StringTree ExprS

instance Eval ExprS where
  evalSym (EI n) = n
  evalSym (EB b) = b
  evalSym EAdd   = (+)
  evalSym EEq    = (==)
  evalSym EIf    = \c a b -> if c then a else b

instance EvalEnv ExprS env where
  compileSym p (EI n) = compileSymDefault signature p (EI n)
  compileSym p (EB b) = compileSymDefault signature p (EB b)
  compileSym p EAdd   = compileSymDefault signature p EAdd
  compileSym p EEq    = compileSymDefault signature p EEq
  compileSym p EIf    = compileSymDefault signature p EIf

