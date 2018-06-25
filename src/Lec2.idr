module Lec2

%default total
%access public export


-- ==2.1 Syntax==


data Ty : Type where
  I  : Ty
  Fn : Ty -> Ty -> Ty

data Cx : Type -> Type where
  ECx : Cx x
  SCx : Cx x -> x -> Cx x
  
data DeB : (t : Ty) -> Cx s -> Type where
  ZI : DeB t (SCx g t)
  SI : DeB t g -> DeB t (SCx g s)

data Tm : Cx Ty -> Ty -> Type where
  Var : DeB t g -> Tm g t
  Lam : Tm (SCx g s) t -> Tm g (Fn s t)
  App : Tm g (Fn s t) -> Tm g s -> Tm g t


-- ==2.2 Semantics==


IntTy : Ty -> Type
IntTy I = Nat
IntTy (Fn s t) = IntTy s -> IntTy t

IntC : Cx Ty -> (Ty -> Type) -> Type
IntC  ECx v      = ()
IntC (SCx g s) v = (IntC g v, v s)

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
fish xz (x :: xs) = fish (SCx xz x) xs

Shub : Cx Ty -> Cx Ty -> Type
Shub g d = (k : List Ty) -> Sub (fish g k) (fish d k)

subp : Shub g d -> Tm g t -> Tm d t
subp x (Var i)     = x [] i
subp x (Lam {s} t) = Lam (subp (\k => x (s :: k)) t)
subp x (App f s)   = App (subp x f) (subp x s)

wkr : Ren g d -> Ren (SCx g s) (SCx d s)
wkr r  ZI    = ZI
wkr r (SI i) = SI (r i)

ren : Ren g d -> Shub g d
ren r [] = Var . r
ren r (q :: qs) = \t => let res = ren (wkr {s=q} r) qs in res t  -- wut

wks : Sub g d -> Sub (SCx g s) (SCx d s)
wks s  ZI = Var ZI
wks s (SI i) = subp (ren SI) (s i)

sub : Sub g d -> Shub g d
sub s [] = s
sub s (q :: qs) = \t => let res = sub (wks {s=q} s) qs in res t  -- wut 
