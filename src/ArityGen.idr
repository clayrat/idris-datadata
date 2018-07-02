module ArityGen 

import Data.Vect

-- 2.2 Arity-Generic Vector Map

arrTy : Vect (S n) Type -> Type
arrTy {n=Z}   (a :: []) = a
arrTy {n=S _} (a :: as) = a -> arrTy as

arrTyVec : {m : Nat} -> Vect (S n) Type -> Type
arrTyVec {n} {m} as = arrTy (replicate (S n) (\a => Vect m a) <*> as)

nvecMap : {m : Nat} -> (n : Nat) -> (as : Vect (S n) Type) -> arrTy as -> arrTyVec {m} as
nvecMap {m} n as f = g n as (replicate m f) 
  where
  g : (x : Nat) -> (xs : Vect (S x) Type) -> Vect y (arrTy xs) -> arrTyVec {m=y} xs
  g Z     (b :: []) h = h
  g (S x) (b :: bs) h = \ys => g x bs (h <*> ys)

cForall : (Vect n a -> Type) -> Type
cForall     {n=Z}   f = f []
cForall {a} {n=S n} f = (x : a) -> cForall {n} (\xs => f (x :: xs)) -- can't do implicit under lambda later on, this leads to more verbose declarations

cLam : {b : Vect n a -> Type} -> ((as : Vect n a) -> b as) -> cForall b
cLam     {n=Z}   f = f []
cLam {a} {n=S n} f = \x => cLam $ \xs => f (x :: xs)

nmap : (n : Nat) -> {m : Nat} -> cForall (\as : Vect (S n) Type => arrTy as -> arrTyVec {m} as)
nmap n {m} = cLam {b=\as => arrTy as -> arrTyVec {m} as} $ nvecMap {m} n 

test1 : nmap {m=3} 1 Int Int (+1) [1,2,3] = [2,3,4]
test1 = Refl

test2 : nmap {m=3} 2 Int Int Int (*) [1,2,3] [4,5,6] = [4,10,18]
test2 = Refl

-- 2.3 Towards Type Genericity 

data Tyc : Type where
  N : Tyc
  U : Tyc
  Prod : Tyc -> Tyc -> Tyc
  Arr : Nat -> Tyc -> Tyc
  Var : Tyc

IntTyc : Tyc -> Type -> Type
IntTyc  N         _ = Nat
IntTyc  U         _ = ()
IntTyc (Prod x y) a = (IntTyc x a, IntTyc y a)
IntTyc (Arr n x)  a = Vect n (IntTyc x a)
IntTyc  Var       a = a

grepeat : (t : Tyc) -> a -> IntTyc t a
grepeat  N         a = Z
grepeat  U         a = ()
grepeat (Prod x y) a = (grepeat x a, grepeat y a)
grepeat (Arr n x)  a = replicate n (grepeat x a)
grepeat  Var       a = a

gzap : (t : Tyc) -> IntTyc t (a -> b) -> IntTyc t a -> IntTyc t b
gzap  N          ab      a      = Z
gzap  U          ab      a      = ()
gzap (Prod x y) (f1,f2) (a1,a2) = (gzap x f1 a1, gzap y f2 a2)
gzap (Arr n x)   ab      a      = replicate n (gzap x) <*> ab <*> a
gzap  Var        ab      a      = ab a

gvecMap : (t : Tyc) -> (n : Nat) -> (as : Vect (S n) Type) -> arrTy as -> arrTy (replicate (S n) (IntTyc t) <*> as)
gvecMap t n as f = g n as (grepeat t f) 
  where
  g : (x : Nat) -> (xs : Vect (S x) Type) -> IntTyc t (arrTy xs) -> arrTy (replicate (S x) (IntTyc t) <*> xs)
  g Z     (b :: []) h = h
  g (S x) (b :: bs) h = \ys => g x bs (gzap t h ys)

gmap : (t : Tyc) -> (n : Nat) -> cForall (\as : Vect (S n) Type => arrTy as -> arrTy (replicate (S n) (IntTyc t) <*> as))
gmap t n = cLam {b=\as => arrTy as -> arrTy (replicate (S n) (IntTyc t) <*> as)} $ gvecMap t n 

test3 : gmap (Arr 2 (Prod Var (Prod Var U))) 1 Int Int (*2) [(1,2,()), (3,4,())] = [(2,4,()),(6,8,())]
test3 = Refl