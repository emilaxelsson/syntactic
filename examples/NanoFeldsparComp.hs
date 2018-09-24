{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

-- Note GADTs needed by GHC 7.6. In later GHCs is works with just TypeFamilies.

-- | A simple compiler for NanoFeldspar

module NanoFeldsparComp where



import Control.Monad.State
import Control.Monad.Writer

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Sharing
import Language.Syntactic.Functional.Tuple

import NanoFeldspar hiding ((==))



--------------------------------------------------------------------------------
-- * Imperative programs
--------------------------------------------------------------------------------

type Var = String

varName :: Name -> Var
varName v = 'v' : show v

varNameE :: Name -> Exp
varNameE v = App (varName v) []

data Exp = App String [Exp]
  deriving (Eq, Show)

data Stmt
    = Assign Exp Exp
    | If Exp Prog Prog
    | For Exp Var Prog
  deriving (Eq, Show)

type Prog = [Stmt]

viewOp :: String -> Maybe String
viewOp op@(_:_:_)
    | head op == '(' && last op == ')' = Just $ tail $ init op
    | otherwise = Nothing

renderExp :: Exp -> String
renderExp (App f []) = f
renderExp (App f@(_:_) [a,b])
    | Just op <- viewOp f = concat ["(", renderExp a, " ", op, " ", renderExp b, ")"]
renderExp (App f args) = "(" ++ unwords (f : Prelude.map renderExp args) ++ ")"

indent :: [String] -> [String]
indent = Prelude.map ("    " ++)

renderProg :: Prog -> String
renderProg = unlines . concatMap render
  where
    render (Assign l r) = [unwords [renderExp l, "=", renderExp r]]
    render (If c t f) = concat
        [ [unwords ["if", renderExp c]]
        , indent (concatMap render t)
        , ["else"]
        , indent (concatMap render f)
        ]
    render (For l v body) = concat
        [ [unwords ["for",v,"<", renderExp l]]
        , indent (concatMap render body)
        ]



--------------------------------------------------------------------------------
-- * Code generation
--------------------------------------------------------------------------------

type CodeGen = WriterT Prog (State Name)

type Dom = BindingT
       :+: Let
       :+: Tuple
       :+: Arithmetic
       :+: Parallel
       :+: ForLoop
       :+: Construct

fresh :: CodeGen Exp
fresh = do
    v <- get; put (v+1)
    return (varNameE v)

confiscate :: CodeGen Exp -> CodeGen (Exp,Prog)
confiscate = censor (const mempty) . listen

compileExp :: ASTF Dom a -> CodeGen Exp
compileExp var
    | Just (VarT v) <- prj var = return (varNameE v)
compileExp (lett :$ a :$ (lam :$ body))
    | Just (Let _)  <- prj lett
    , Just (LamT v) <- prj lam
    = do
        a' <- compileExp a
        tell [Assign (varNameE v) a']
        compileExp body
compileExp (par :$ len :$ (lam :$ body))
    | Just Parallel <- prj par
    , Just (LamT v) <- prj lam
    = do
        len' <- compileExp len
        (e,body') <- confiscate $ compileExp body
        arr <- fresh
        let arrPos = App "(!)" [arr, varNameE v]
        tell
            [ For len' (varName v)
                (  body'
                ++ [Assign arrPos e]
                )
            ]
        return arr
compileExp (for :$ len :$ init :$ (lam1 :$ (lam2 :$ body)))
    | Just ForLoop  <- prj for
    , Just (LamT i) <- prj lam1
    , Just (LamT s) <- prj lam2
    = do
        len'  <- compileExp len
        init' <- compileExp init
        (e,body') <- confiscate $ compileExp body
        next <- fresh
        tell
            [ Assign (varNameE s) init'
            , For len' (varName i)
                (  body'
                ++ [ Assign next e
                   , Assign (varNameE s) next
                   ]
                )
            ]
        return next
compileExp (cond :$ c :$ t :$ f)
    | Just (Construct "cond" _) <- prj cond
    = do
        c' <- compileExp c
        (t',tProg) <- confiscate $ compileExp t
        (f',fProg) <- confiscate $ compileExp f
        res <- fresh
        tell
            [ If c'
                (  tProg
                ++ [Assign res  t']
                )
                (  fProg
                ++ [Assign res  f']
                )
            ]
        return res
compileExp (arrIx :$ arr :$ ix)
    | Just (Construct "arrIx" _) <- prj arrIx = do
        arr' <- compileExp arr
        ix'  <- compileExp ix
        return $ App "(!)" [arr',ix']
-- Generic case for all other constructs
compileExp a = simpleMatch
  (\s as -> fmap (App (renderSym s)) $ sequence (listArgs compileExp as)) a

compileTop :: ASTF Dom a -> CodeGen ()
compileTop = go 0
  where
    go :: Int -> ASTF Dom a -> CodeGen ()
    go n (lam :$ body)
        | Just (LamT v) <- prj lam = do
            tell [Assign (varNameE v) (App ("inp" ++ show n) [])]
            go (n+1) body
    go _ a = do
        a' <- compileExp a
        tell [Assign (App "out" []) a']



compile :: (Syntactic a, Domain a ~ Typed Dom) => a -> String
compile
    = renderProg
    . fst
    . flip runState 0
    . execWriterT
    . compileTop
    . mapAST (\(Typed s) -> s)
    . codeMotion cmInterface
    . desugar

icompile :: (Syntactic a, Domain a ~ Typed Dom) => a -> IO ()
icompile = putStrLn . compile



--------------------------------------------------------------------------------
-- * Code generation
--------------------------------------------------------------------------------

test_matMul = icompile matMul

