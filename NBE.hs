-- Normalisation by evaluation for an untyped lambda calculus.
-- Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
{-# LANGUAGE KindSignatures, DataKinds, GADTs, TypeOperators, TypeFamilies,
    OverloadedStrings #-}
module NBE where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Debug.Trace
import Control.Monad.State
import Control.Applicative
import GHC.Exts (IsString(..))

data Sym = Sym { nameOf :: !String, symId :: !Int } deriving (Eq, Ord)
instance Show Sym where show (Sym s 0) = s; show (Sym s i) = s ++ show i
instance IsString Sym where fromString s = Sym s 0

data Type = Base | !Type :=> !Type deriving (Show, Eq, Ord)

data Term = TVar !Sym | TApp !Term !Term | TLam !Sym !Term
data NF = Lam !Sym !NF | Atom !NE
data NE = Var !Sym | App !NE !NF

instance Show Term where
  show (TVar x) = show x
  show m@TApp{} = "(" ++ showApp m ++ ")"
    where showApp (TApp x y) = showApp x ++ " " ++ show y
          showApp m = show m
  show (TLam x y) = "(λ" ++ show x ++ ". " ++ show y ++ ")"

class ToTerm a where toTerm :: a -> Term
instance ToTerm NF where toTerm (Lam x m) = TLam x (toTerm m); toTerm (Atom x) = toTerm x
instance ToTerm NE where toTerm (Var x) = TVar x; toTerm (App x y) = TApp (toTerm x) (toTerm y)
instance Show NE where show = show . toTerm
instance Show NF where show = show . toTerm

-- A monad for generating fresh variables.
type Eval a = State Int a
gensym :: String -> Eval Sym
gensym s = Sym s <$> (modify (+1) >> get)
runEval :: Eval a -> a
runEval s = evalState s 0

-- An NBE semantic value is either a neutral term or a function.
-- The function is monadic, since it may need to make fresh variables.
data Sem = Neut !NE | Func !(Sem -> Eval Sem)
-- An environment map variables to semantic values.
type Env = Map Sym Sem

instance Show Sem where show (Neut n) = show n; show Func{} = "<fn>"

app :: Sem -> Sem -> Eval Sem
app (Func f) x = f x
app (Neut n) x = Neut . App n <$> reify x

eval :: Env -> Term -> Eval Sem
-- If the variable is bound, return its binding; otherwise, return it as syntax.
eval env (TVar v) = pure $ Map.findWithDefault (Neut (Var v)) v env
eval env (TApp m n) = join (app <$> eval env m <*> eval env n)
eval env (TLam v m) = pure . Func $ \x -> eval (Map.insert v x env) m

reify :: Sem -> Eval NF
reify (Neut n) = pure $ Atom n
reify (Func f) = do x <- gensym "_"
                    Lam x <$> (reify =<< f (reflect (Var x)))

-- Reflect is easy because we're "intensional", and don't bother eta-expanding
-- variables of non-base type. (Indeed, we ignore types entirely.)
reflect :: NE -> Sem
reflect = Neut

-- Normalisation by evaluation!
norm :: Term -> Eval NF
norm = eval Map.empty >=> reify

-- Try (runEval (norm tExample)).
-- You should get (Atom (Var "y")).
tId, tExample :: Term
tId = TLam "x" (TVar "x")
tExample = TApp tId (TVar "y")
