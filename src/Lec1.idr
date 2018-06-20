module Lec1

import Data.Vect
import Control.Monad.Identity
import Control.Algebra.NumericImplementations
import Interfaces.Verified

import Util

%default total
%access public export


-- ==1.1==


zipPrf : (ss : List s) -> (ts : List t) -> length ss = length ts -> length (zip ss ts) = length ss
zipPrf []        []        Refl = Refl
zipPrf []        (_ :: _)  prf = absurd prf
zipPrf (_ :: _)  []        prf = absurd prf
zipPrf (_ :: xs) (_ :: ys) prf = cong $ zipPrf xs ys $ succInjective (length xs) (length ys) prf


-- ==1.2==


-- ex 1.1
-- `vec`=`replicate`

-- ex 1.2
-- `vapp`=`<*>`

-- ex 1.3
vmap : (s -> t) -> Vect n s -> Vect n t
vmap {n} f ss = replicate n f <*> ss

-- ex 1.4
vzip : Vect n s -> Vect n t -> Vect n (s,t)
vzip {n} ss ts = replicate n MkPair <*> ss <*> ts

-- ex 1.5
-- proj = `index`
tabulate : (Fin n -> x) -> Vect n x
tabulate {n=Z}   _ = []
tabulate {n=S k} f = f FZ :: tabulate {n=k} (f . FS)

-- helper for later
fill : Vect n (Fin n)
fill = tabulate id


-- ==1.3==


-- see also Data.Combinators.Applicative @ contrib
[ftorFun] Functor (\x => s -> x) where
  map f a = f . a

using implementation ftorFun
  [appFun] Applicative (\x => s -> x) where
    pure a = \_ => a            -- k: drop env
    f <*> fa = \s => f s (fa s) -- s: share env

-- ex 1.6
-- `diag (map f m)` in stdlib

-- ex 1.7
-- `Control.Monad.Identity`
data CompF : (f : b -> c) -> (g : a -> b) -> (x : a) -> Type where
  MkCompF : f (g a) -> CompF f g a

(Functor f, Functor g) => Functor (CompF f g) where
  map f (MkCompF fga) = MkCompF $ map (map f) fga

(Applicative f, Applicative g) => Applicative (CompF f g) where
  pure a = MkCompF $ pure $ pure a
  (MkCompF f) <*> (MkCompF fga) = MkCompF $ (map (<*>) f) <*> fga

-- ex 1.8

--[constFun] Functor (\_ => x) where
--  map _ a = a
--
--using implementation constFun
--  [constMon] (Monoid x) => Applicative (\_ => x) where
--    pure _ = neutral
--    fa <*> f = fa <+> f

-- this gets ugly later, switching to a wrapper

data Const : Type -> Type -> Type where
  MkConst : a -> Const a b

getConst : Const a b -> a
getConst (MkConst a) = a

Functor (Const a) where
  map _ (MkConst b) = MkConst b

Monoid a => Applicative (Const a) where
  pure _ = MkConst neutral
  (MkConst f) <*> (MkConst fa) = MkConst (f <+> fa)

-- ex 1.9

data ProdF : (f : a -> b) -> (g : a -> b) -> (x : a) -> Type where
  MkProdF : f a -> g a -> ProdF f g a

(Functor f, Functor g) => Functor (ProdF f g) where
  map f (MkProdF fa ga) = MkProdF (map f fa) (map f ga)

(Applicative f, Applicative g) => Applicative (ProdF f g) where
  pure a = MkProdF (pure a) (pure a)
  (MkProdF f g) <*> (MkProdF fa ga) = MkProdF (f <*> fa) (g <*> ga)

-- ex 1.10

vtranspose : {n : Nat} -> Vect m (Vect n x) -> Vect n (Vect m x)
vtranspose = sequence

--using implementation constMon
crush : (Traversable f, Monoid y) => (x -> y) -> f x -> y
crush {y} f fx = getConst $ traverse {b=()} (MkConst .% f) fx -- b is arbitrary since it's dropped

-- ex 1.11

Foldable Identity where
  foldr f i (Id x) = f x i

Traversable Identity where
  traverse f (Id x) = map Id $ f x

(Foldable f, Foldable g) => Foldable (CompF f g) where
  foldr f i (MkCompF fga) = foldr (\ge, j => foldr f j ge) i fga

(Traversable f, Traversable g) => Traversable (CompF f g) where
  traverse f (MkCompF fga) = map MkCompF $ traverse (traverse f) fga


-- ==1.4==


-- Eith : Type -> Type -> Type
-- Eith a b = (c : Bool ** if c then a else b)
--
-- duncurry : {S : Type} -> {T : S -> Type} -> {P : (s : S ** T s) -> Type} -> ((s : S) -> (t : T s) -> P (s ** t)) -> (p : (s : S ** T s)) -> P p
-- duncurry f (s ** t) = f s t


-- ==1.5==


-- ex 1.12
-- Nat.`plus` & `mult`


-- ==1.6==


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

-- ex 1.13

nPair : (f, g : Normal) -> (Interp f x, Interp g x) -> Interp (TimesN f g) x
nPair (MkNormal _ _) (MkNormal _ _) ((s1 ** xs1), (s2 ** xs2)) = ((s1, s2) ** xs1 ++ xs2)

nPairSur : (f, g : Normal) -> Interp (TimesN f g) x -> (Interp f x, Interp g x)
nPairSur (MkNormal _ size1) (MkNormal _ _) ((s1, s2) ** xs0) = ((s1 ** take (size1 s1) xs0), (s2 ** drop (size1 s1) xs0))

-- ex 1.14

[lnSemi] Semigroup (Interp ListN x) where
  (s1 ** xs1) <+> (s2 ** xs2) = (s1 + s2 ** xs1 ++ xs2)

using implementation lnSemi
  [lnMon] Monoid (Interp ListN x) where
    neutral = (Z ** [])

--[funFold] Functor (Interp n) where
--  map {n=MkNormal _ _} f (s ** xs) = (s ** map f xs)
--
--[normFold] Foldable (Interp n) where
--  foldr {n=MkNormal _ _} f init (_ ** xs) = foldr f init xs
--  foldl {n=MkNormal _ _} f init (_ ** xs) = foldl f init xs -- can't use default implementation here

-- named implementations break down at this point, it can't find `normFold` no matter what
--
--using implementation normFold
--  using implementation funFold
--    [normTrav] Traversable (Interp n) where
--      traverse {n=MkNormal _ _} f (s ** xs) = map (MkDPair s) (traverse f xs)

-- wrapper workaround
data InterpN : Type -> Type where
  MkInterpN : Interp n t -> InterpN t

Functor InterpN where
  map f (MkInterpN {n=MkNormal sh sz} (s ** xs)) = MkInterpN {n=MkNormal sh sz} (s ** map f xs)

Foldable InterpN where
  foldr f init (MkInterpN {n=MkNormal _ _} (_ ** xs)) = foldr f init xs

Traversable InterpN where
  traverse f (MkInterpN {n=MkNormal sh sz} (s ** xs)) = map (MkInterpN {n=MkNormal sh sz} .% MkDPair s) (traverse f xs)

using implementation PlusNatMonoid
  CompN : Normal -> Normal -> Normal
  CompN (MkNormal shf szf) (MkNormal shg szg) = MkNormal (Interp (MkNormal shf szf) shg) (crush {f=InterpN} szg . MkInterpN {n=MkNormal shf szf})

  sizeT : Traversable t => t x -> Nat
  sizeT = crush (const 1)

normalT : Traversable t => Normal
normalT {t} = MkNormal (t ()) sizeT

shapeT : Traversable t => t a -> t ()
shapeT = runIdentity . traverse (const $ Id ())

one : x -> Interp ListN x
one x = (1 ** [x])

using implementation lnMon
  contentsT : Traversable t => t x -> Interp ListN x
  contentsT = crush one

-- ex 1.15

ImpN : Normal -> Normal -> Type
ImpN f g = (s : Shape f) -> Interp g (Fin (size f s))

nMorph : ImpN f g -> Interp f x -> Interp g x
nMorph {f=MkNormal _ _} {g=MkNormal _ _} ifg (s ** xs) =
  let (s2 ** xs2) = ifg s in
  (s2 ** map (\fin => index fin xs) xs2)

morphN : ({x : Type} -> Interp f x -> Interp g x) -> ImpN f g
morphN {f=MkNormal _ _} {g=MkNormal _ _} ifig s = ifig (s ** fill)

-- ex 1.16

TensorN : Normal -> Normal -> Normal
TensorN (MkNormal sh1 sz1) (MkNormal sh2 sz2) = MkNormal (sh1, sh2) (\(s1, s2) => sz1 s1 * sz2 s2)

swap : (f, g: Normal) -> (f `TensorN` g) `ImpN` (g `TensorN` f)
swap (MkNormal sh1 sz1) (MkNormal sh2 sz2) (s1, s2) = ((s2, s1) ** rewrite multCommutative (sz2 s2) (sz1 s1) in fill)

using implementation PlusNatMonoid  -- for the lemma
  drop : (f, g: Normal) -> (f `TensorN` g) `ImpN` (g `CompN` f)
  drop (MkNormal sh1 sz1) (MkNormal sh2 sz2) (s1, s2) =
    ((s2 ** replicate (sz2 s2) s1) **
      let lem = travConstLemma s1 (sz2 s2) sz1
          eq = sym $ cong {t=Const Nat (Vect (sz2 s2) ())}
                          {f=\z=> Vect (getConst $ map (MkInterpN {n=MkNormal sh2 sz2} .% MkDPair s2) z) (Fin (sz1 s1 * sz2 s2))}
                          lem  --"implicit" my ass
         in
      replace {P=id} eq fill)
    where
    travConstLemma : (x : a) -> (n: Nat) -> (f : a -> Nat) -> traverse (MkConst .% f) (Vect.replicate n x) = MkConst (f x * n)
    travConstLemma x Z     f = cong $ sym $ multZeroRightZero (f x)
    travConstLemma x (S k) f = trans (cong {f=\z=>(MkConst (f x)) <*> z} (travConstLemma x k f)) --rewrites don't work well here either
                                     (sym $ cong {f=MkConst} (multRightSuccPlus (f x) k))


-- ==1.7==


-- ex 1.17
using implementation lnSemi
  [lnVSemi] VerifiedSemigroup (Interp ListN x) where
    semigroupOpIsAssociative     (Z   ** [])       (sc ** xsc) (sr ** xsr) = Refl
    semigroupOpIsAssociative {x} (S k ** l :: xsl) (sc ** xsc) (sr ** xsr) =
      cong {f=\nxs=>MkDPair (S (DPair.fst nxs)) (l :: (DPair.snd nxs))} $
      assert_total $ -- Idris can't see decreases inside sigmas
      semigroupOpIsAssociative (k ** xsl) (sc ** xsc) (sr ** xsr)

using implementation lnMon
  using implementation lnVSemi
    [lnVMon] VerifiedMonoid (Interp ListN x) where
      monoidNeutralIsNeutralL (Z   ** [])    = Refl
      monoidNeutralIsNeutralL (S k ** x::xs) =
        cong {f=\nxs=>MkDPair (S (DPair.fst nxs)) (x :: DPair.snd nxs) } $
        assert_total $
        monoidNeutralIsNeutralL (k ** xs)
      monoidNeutralIsNeutralR (s**xs) = Refl

-- ex 1.18
-- it's `vectAppendAssociative` in Data.Vect
-- the main issue in Idris is the IH case - the vanilla `cong` gets stuck on the associativity of lengths

interface (Monoid x, Monoid y) => MonoidHom x y (f : x -> y) where
  respNeutral : f Algebra.neutral = Algebra.neutral
  respOp : (a, b : x) -> f (a <+> b) = f a <+> f b

using implementation PlusNatMonoid
  using implementation lnMon
    [fstHom] MonoidHom (Interp ListN x) Nat DPair.fst where
      respNeutral = Refl
      respOp (sa ** xsa) (sb ** xsb) = Refl

-- ex 1.19

VerifiedFunctor (Vect n) where
  functorIdentity []      = Refl
  functorIdentity (x::xs) = cong $ functorIdentity xs
  functorComposition []      g1 g2 = Refl
  functorComposition (x::xs) g1 g2 = cong $ functorComposition xs g1 g2


-- ==1.8==


