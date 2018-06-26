module Lec2

%default total
%access public export


-- ==2.1 Syntax==


data Ty : Type where
  I  : Ty
  Fn : Ty -> Ty -> Ty

data Cx : Type -> Type where
  NCx : Cx x
  CCx : Cx x -> x -> Cx x
  
data DeB : (t : Ty) -> Cx s -> Type where
  ZI : DeB t (CCx g t)
  SI : DeB t g -> DeB t (CCx g s)

data Tm : Cx Ty -> Ty -> Type where
  Var : DeB t g -> Tm g t
  Lam : Tm (CCx g s) t -> Tm g (Fn s t)
  App : Tm g (Fn s t) -> Tm g s -> Tm g t


-- ==2.2 Semantics==


IntTy : Ty -> Type
IntTy I = Nat
IntTy (Fn s t) = IntTy s -> IntTy t

IntC : Cx Ty -> (Ty -> Type) -> Type
IntC  NCx v      = ()
IntC (CCx g s) v = (IntC g v, v s)

IntD : DeB t g -> IntC g v -> v t
IntD  ZI    (g, t) = t
IntD (SI i) (g, s) = IntD i g

IntTm : Tm g t -> IntC g IntTy -> IntTy t
IntTm (Var i)   g = IntD i g
IntTm (Lam t)   g = \s => IntTm t (g, s)
IntTm (App f s) g = IntTm f g (IntTm s g)


-- ==2.3 Substitution==


Ren : Cx Ty -> Cx Ty -> Type
Ren g d = {t : Ty} -> DeB t g -> DeB t d

Sub : Cx Ty -> Cx Ty -> Type
Sub g d = {t : Ty} -> DeB t g -> Tm d t

fish : Cx x -> List x -> Cx x
fish xz [] = xz
fish xz (x :: xs) = fish (CCx xz x) xs

Shub : Cx Ty -> Cx Ty -> Type
Shub g d = (k : List Ty) -> Sub (fish g k) (fish d k)

subp : Shub g d -> Tm g t -> Tm d t
subp x (Var i)     = x [] i
subp x (Lam {s} t) = Lam (subp (\k => x (s :: k)) t)
subp x (App f s)   = App (subp x f) (subp x s)

wkr : Ren g d -> Ren (CCx g s) (CCx d s)
wkr r  ZI    = ZI
wkr r (SI i) = SI (r i)

ren : Ren g d -> Shub g d
ren r [] = Var . r
ren r (q :: qs) = \t => let res = ren (wkr {s=q} r) qs in res t  -- wut

wks : Sub g d -> Sub (CCx g s) (CCx d s)
wks s  ZI = Var ZI
wks s (SI i) = subp (ren SI) (s i)

sub : Sub g d -> Shub g d
sub s [] = s
sub s (q :: qs) = \t => let res = sub (wks {s=q} s) qs in res t  -- wut 


-- ==2.4 Convenience==


weak : (k : List Ty) -> Ren g (fish g k)
weak []      i = i
weak (q::qs) i = weak qs (SI i)

-- this won't work without `auto` but neither will the one below
lambda : {auto k : List Ty} -> (Tm (fish (CCx g s) k) s -> Tm (CCx g s) t) -> Tm g (Fn s t)
lambda {k} f = Lam (f $ Var $ weak k ZI)

test : Tm NCx (Fn I I) 
test = lambda $ \x => x

------ this part becomes kinda superfluous then, though the equality-based search is probably more robust
chips : Cx x -> List x -> List x
chips NCx ys = ys
chips (CCx xz x) ys = chips xz (x :: ys)

-- ex 2.1

lem1 : (g : Cx x) -> (k : List x) -> fish g k = fish NCx (chips g k)
lem1  NCx       k = Refl
lem1 (CCx gs g) k = lem1 gs (g :: k)

lem : (d, g : Cx x) -> chips d [] = chips g k -> fish g k = d
lem {k} d g prf = 
  rewrite lem1 d [] in 
  rewrite lem1 g k in 
  cong {f=fish NCx} $ sym prf 

lambda' : {auto i : chips d [] = chips g (s::k)} -> (Tm d s -> Tm (CCx g s) t) -> Tm g (Fn s t)
lambda' {d} {g} {s} {k} {i} f = Lam (f $ rewrite sym $ lem d (CCx g s) i in Var $ weak k ZI)

test' : Tm NCx (Fn (Fn I I) (Fn I I))
test' = lambda' $ \f => lambda' $ \x => App f (App f x)
------


-- ==2.5 Hereditary==

mutual 
  data NF : Cx Ty -> Ty -> Type where
    LamN : NF (CCx g s) t -> NF g (Fn s t)
    AppN : DeB t g -> Spi g t -> NF g I
    
  data Spi : Cx Ty -> Ty -> Type where
    NSp : Spi g I
    CSp : NF g s -> Spi g t -> Spi g (Fn s t)


-- ex 2.2    

remove : (g : Cx Ty) -> (x : DeB t g) -> Cx Ty
remove {t} (CCx x t)  ZI    = x
remove     (CCx x s) (SI y) = CCx (remove x y) s

thin : (x : DeB s g) -> Ren (remove g x) g
thin  ZI     y     = SI y
thin (SI _)  ZI    = ZI
thin (SI x) (SI y) = SI (thin x y)

data Veq : DeB s g -> DeB t g -> Type where
  Same : Veq x x
  Diff : (y : DeB t (remove g x)) -> Veq x (thin x y)

-- ex 2.3

veq : (x : DeB s g) -> (y : DeB t g) -> Veq x y
veq   ZI     ZI    = Same
veq   ZI    (SI y) = Diff y
veq  (SI x)  ZI    = Diff ZI
veq  (SI x) (SI y) with (veq x y)
  veq  (SI x) (SI x)          | Same   = Same
  veq  (SI x) (SI (thin x p)) | Diff p = Diff $ SI p

-- ex 2.4

mutual 
  renNm : Ren g d -> NF g t -> NF d t
  renNm r (LamN n)   = LamN (renNm (wkr r) n)
  renNm r (AppN v s) = AppN (r v) (renSp r s)

  renSp : Ren g d -> Spi g t -> Spi d t
  renSp r  NSp      = NSp
  renSp r (CSp n s) = CSp (renNm r n) (renSp r s)