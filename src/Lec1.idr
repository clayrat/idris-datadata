module Lec1

import Data.Vect
import Control.Monad.Identity

import Control.Algebra.NumericImplementations -- for testing

%default total
%access public export

zipPrf : (ss : List s) -> (ts : List t) -> length ss = length ts -> length (zip ss ts) = length ss  
zipPrf []        []        Refl = Refl
zipPrf []        (_ :: _)  prf = absurd prf
zipPrf (_ :: _)  []        prf = absurd prf
zipPrf (_ :: xs) (_ :: ys) prf = cong $ zipPrf xs ys $ succInjective (length xs) (length ys) prf

-- 1.1
-- `vec`=`replicate`

-- 1.2
-- `vapp`=`<*>`

-- 1.3
vmap : (s -> t) -> Vect n s -> Vect n t
vmap {n} f ss = replicate n f <*> ss

-- 1.4
vzip : Vect n s -> Vect n t -> Vect n (s,t)
vzip {n} ss ts = replicate n MkPair <*> ss <*> ts

-- 1.5
-- proj = `index`
tabulate : (Fin n -> x) -> Vect n x
tabulate {n=Z}   _ = []
tabulate {n=S k} f = f FZ :: tabulate {n=k} (f . FS)

-- see also Data.Combinators.Applicative @ contrib
[ftorFun] Functor (\x => s -> x) where
  map f a = f . a

using implementation ftorFun  
  [appFun] Applicative (\x => s -> x) where
    pure a = \_ => a            -- k: drop env
    f <*> fa = \s => f s (fa s) -- s: share env

-- 1.6
-- `diag (map f m)` in stdlib

-- 1.7
-- `Control.Monad.Identity`
data CompF : (f : b -> c) -> (g : a -> b) -> (x : a) -> Type where
  MkCompF : f (g a) -> CompF f g a

(Functor f, Functor g) => Functor (CompF f g) where
  map f (MkCompF fga) = MkCompF $ map (map f) fga

(Applicative f, Applicative g) => Applicative (CompF f g) where
  pure a = MkCompF $ pure $ pure a
  (MkCompF f) <*> (MkCompF fga) = MkCompF $ (map (<*>) f) <*> fga

-- 1.8

data Const : Type -> Type -> Type where
  MkConst : a -> Const a b

getConst : Const a b -> a  
getConst (MkConst a) = a

Functor (Const a) where
  map _ (MkConst b) = MkConst b

Monoid a => Applicative (Const a) where
  pure _ = MkConst neutral
  (MkConst f) <*> (MkConst fa) = MkConst (f <+> fa)

--[constFun] Functor (\_ => x) where
--  map _ a = a
--
--using implementation constFun
--  [constMon] (Monoid x) => Applicative (\_ => x) where
--    pure _ = neutral
--    fa <*> f = fa <+> f

-- 1.9
data ProdF : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  MkProdF : f a -> g a -> ProdF f g a

(Functor f, Functor g) => Functor (ProdF f g) where
  map f (MkProdF fa ga) = MkProdF (map f fa) (map f ga)

(Applicative f, Applicative g) => Applicative (ProdF f g) where
  pure a = MkProdF (pure a) (pure a)
  (MkProdF f g) <*> (MkProdF fa ga) = MkProdF (f <*> fa) (g <*> ga)

-- 1.10
vtranspose : {n : Nat} -> Vect m (Vect n x) -> Vect n (Vect m x)
vtranspose = sequence

--using implementation constMon
crush : (Traversable f, Monoid y) => (x -> y) -> f x -> y
crush {y} f fx = getConst $ traverse {b=()} (MkConst . f) fx -- b is arbitrary since it's dropped

-- 1.11
Foldable Identity where
  foldr f i (Id x) = f x i

Traversable Identity where
  traverse f (Id x) = map Id $ f x

(Foldable f, Foldable g) => Foldable (CompF f g) where
  foldr f i (MkCompF fga) = foldr (\ge, j => foldr f j ge) i fga

(Traversable f, Traversable g) => Traversable (CompF f g) where
  traverse f (MkCompF fga) = map MkCompF $ traverse (traverse f) fga

-- will we need these?  
Eith : Type -> Type -> Type
Eith a b = (c : Bool ** if c then a else b)  

duncurry : {S : Type} -> {T : S -> Type} -> {P : (s : S ** T s) -> Type} -> ((s : S) -> (t : T s) -> P (s ** t)) -> (p : (s : S ** T s)) -> P p
duncurry f (s ** t) = f s t 

-- 1.12
-- Nat.`plus` & `mult`

record Normal where
  constructor MkNormal
  Shape : Type
  size : Shape -> Nat

Interp : Normal -> Type -> Type
Interp (MkNormal shape size) x = (s : shape ** Vect (size s) x)

VectN : Nat -> Normal
VectN n = MkNormal () (const n)

ListN : Normal
ListN = MkNormal Nat id

KN : Type -> Normal
KN a = MkNormal a (const 0)

IKN : Normal 
IKN = VectN 1

PlusN : Normal -> Normal -> Normal
PlusN (MkNormal sh1 s1) (MkNormal sh2 s2) = MkNormal (Either sh1 sh2) (either s1 s2) 

TimesN : Normal -> Normal -> Normal
TimesN (MkNormal sh1 s1) (MkNormal sh2 s2) = MkNormal (sh1, sh2) (\(a, b) => s1 a + s2 b)

nInj : (f, g : Normal) -> Either (Interp f x) (Interp g x) -> Interp (PlusN f g) x
nInj (MkNormal _ _) (MkNormal _ _) (Left (s ** xs))  = (Left  s ** xs)
nInj (MkNormal _ _) (MkNormal _ _) (Right (s ** xs)) = (Right s ** xs)

data InvImg : (x -> y) -> y -> Type where
  From : (a : x) -> InvImg f (f a)

nCase : (f, g : Normal) -> (sum : Interp (PlusN f g) x) -> InvImg (nInj f g) sum
nCase (MkNormal _ _) (MkNormal _ _) (Left  s ** xs) = From $ Left (s ** xs)
nCase (MkNormal _ _) (MkNormal _ _) (Right s ** xs) = From $ Right (s ** xs)

nOut : (f, g : Normal) -> Interp (PlusN f g) x -> Either (Interp f x) (Interp g x)
nOut f g xs0 with (nCase f g xs0)
  nOut f g (nInj f g xs) | From xs = xs

-- 1.13

nPair : (f, g : Normal) -> (Interp f x, Interp g x) -> Interp (TimesN f g) x
nPair (MkNormal _ _) (MkNormal _ _) ((s1 ** xs1), (s2 ** xs2)) = ((s1, s2) ** xs1 ++ xs2)

nPairSur : (f, g : Normal) -> Interp (TimesN f g) x -> (Interp f x, Interp g x)
nPairSur (MkNormal _ size1) (MkNormal _ _) ((s1, s2) ** xs0) = ((s1 ** take (size1 s1) xs0), (s2 ** drop (size1 s1) xs0))
