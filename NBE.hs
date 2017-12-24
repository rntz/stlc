{-# LANGUAGE KindSignatures, DataKinds, GADTs, TypeOperators, TypeFamilies #-}
module NBE where

import Data.Map.Strict
import qualified Data.Map.Strict as Map
import Debug.Trace

data Type = Base | !Type :=> !Type deriving (Show, Eq, Ord)

type Var = String
data Term = TVar !Var | TApp !Term !Term | TLam !Var !Term deriving Show
data NF = Lam !Var !NF | Neu !NE deriving Show
data NE = Var !Var | App !NE !NF deriving Show

-- An NBE semantic value is either a neutral term or a function.
-- An environment map variables to semantic values.
data Sem = Neut !NE | Func !(Sem -> Sem)
type Env = Map Var Sem

instance Show Sem where
    show (Neut n) = show n
    show (Func f) = "<func>"

app :: Sem -> Sem -> Sem
app (Func f) x = f x
app (Neut n) x = Neut (App n (reify x))

eval :: Env -> Term -> Sem
-- If the variable is bound, return its binding; otherwise, return it as syntax.
eval s (TVar v) = findWithDefault (Neut (Var v)) v s
eval s (TApp m n) = app (eval s m) (eval s n)
eval s (TLam v m) = Func $ \x -> eval (insert v x s) m

reify :: Sem -> NF
reify (Neut n) = Neu n
reify (Func f) = Lam x (reify (f (reflect (Var x))))
    where x = undefined -- argh, needs to be fresh!

reflect :: NE -> Sem
reflect = Neut -- that was easy!

normalize :: Term -> NF
normalize m = reify (eval empty m)

-- Try running (normalize tExample).
-- You should get (Neu (Var "y")).
tId, tExample :: Term
tId = TLam "x" (TVar "x")
tExample = TApp tId (TVar "y")
