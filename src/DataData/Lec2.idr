module DataData.Lec2

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

IntCx : Cx Ty -> (Ty -> Type) -> Type
IntCx  NCx      _ = ()
IntCx (CCx g s) v = (IntCx g v, v s)

IntD : DeB t g -> IntCx g v -> v t
IntD  ZI    (g, t) = t
IntD (SI i) (g, s) = IntD i g

IntTm : Tm g t -> IntCx g IntTy -> IntTy t
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

-- ex 2.5

mutual 
  herSubNF : (x : DeB s g) -> NF (remove g x) s -> NF g t -> NF (remove g x) t
  herSubNF x s (LamN n)   = LamN $ herSubNF (SI x) (renNm SI s) n
  herSubNF x s (AppN w z) with (veq x w)
    herSubNF x s (AppN x z)          | Same   = appNFSpi s (herSubSpi x s z)
    herSubNF x s (AppN (thin x p) z) | Diff p = AppN p (herSubSpi x s z)

  herSubSpi : (x : DeB s g) -> NF (remove g x) s -> Spi g t -> Spi (remove g x) t
  herSubSpi x s NSp       = NSp
  herSubSpi x s (CSp z w) = CSp (herSubNF x s z) (herSubSpi x s w)

  appNFSpi : NF g t -> Spi g t -> NF g I
  appNFSpi f         NSp      = f
  appNFSpi (LamN b) (CSp m s) = appNFSpi (herSubNF ZI m b) s

-- ex 2.6

mutual
  eta : DeB s g -> NF g s
  eta v = eta' (\d => AppN (weak d v))
  
  eta' : ((d : List Ty) -> Spi (fish g d) s -> NF (fish g d) I) -> NF g s
  eta' {s=I}      c = c [] NSp
  eta' {s=Fn s t} c = LamN (eta' $ \d, sp => c (s :: d) (CSp (eta (weak d ZI)) sp))

normalize : Tm g t -> NF g t
normalize (Var v) = eta v
normalize (Lam t) = LamN (normalize t)
normalize (App f s) with (normalize f, normalize s)
  normalize (App f s) | (LamN t, s') = herSubNF ZI s' t

try1 : NF NCx (((I `Fn` I) `Fn` (I `Fn` I)) `Fn` ((I `Fn` I) `Fn` (I `Fn` I)))
try1 = normalize (lambda' $ \x => x)

church2 : Tm NCx ((t `Fn` t) `Fn` (t `Fn` t)) 
church2 = lambda' $ \f => lambda' $ \x => App f (App f x)

try2 : NF NCx ((I `Fn` I) `Fn` (I `Fn` I))
try2 = normalize (App (App church2 church2) church2)


-- ==2.6 NbE==


data Stop : Cx Ty -> Ty -> Type where
  VarS : DeB t g -> Stop g t
  AppS : Stop g (Fn s t) -> NF g s -> Stop g t

-- ex 2.7

renSt : Ren g d -> Stop g t -> Stop d t
renSt r (VarS x)   = VarS (r x)
renSt r (AppS s n) = AppS (renSt r s) (renNm r n)

stopSp : Stop g t -> Spi g t -> NF g I
stopSp (VarS x)   ss = AppN x ss
stopSp (AppS s n) ss = stopSp s (CSp n ss)

mutual 
  Val : Cx Ty -> Ty -> Type
  Val g t = Either (Go g t) (Stop g t)

  Go : Cx Ty -> Ty -> Type
  Go g  I       = Void
  Go g (Fn s t) = {d : Cx Ty} -> Ren g d -> Val d s -> Val d t

-- ex 2.8

renVal : (t : Ty) -> Ren g d -> Val g t -> Val d t
renVal  I       r (Left g)  = absurd g
renVal (Fn s t) r (Left g)  = Left $ \r',g' => g (r' . r) g'
renVal  t       r (Right s) = Right (renSt r s)

renVals : (t : Cx Ty) -> Ren g d -> IntCx t (Val g) -> IntCx t (Val d)
renVals  NCx       r ()      = ()
renVals (CCx ts t) r (ti, v) = (renVals ts r ti, renVal t r v)

idEnv : (g : Cx Ty) -> IntCx g (Val g)
idEnv  NCx       = ()
idEnv (CCx gs g) = (renVals gs SI (idEnv gs), Right $ VarS ZI)

-- ex 2.9

mutual
  applyVal : Val g (Fn s t) -> Val g s -> Val g t
  applyVal     (Left f)  v = f id v
  applyVal {s} (Right f) v = Right $ AppS f (quoteVal s v)

  quoteVal : (t : Ty) -> Val g t -> NF g t
  quoteVal  I       (Left v)  = absurd v
  quoteVal (Fn s t) (Left v)  = LamN (quoteVal t (v SI (Right $ VarS ZI)))
  quoteVal  t       (Right v) = eta' (\d => stopSp (renSt (weak d) v))

-- ex 2.10

eval : Tm g t -> IntCx g (Val d) -> Val d t
eval     (Var  ZI)    (gi, v) = v
eval     (Var (SI i)) (gi, v) = assert_total $ eval (Var i) gi   -- not sure why it can't see `gi`
eval {g} (Lam t)       gi     = Left $ \r, v => eval t (renVals g r gi, v)
eval     (App f s)     gi     = applyVal (eval f gi) (eval s gi)

normByEval : Tm g t -> NF g t 
normByEval {g} {t} tm = quoteVal t (eval tm (idEnv g))

try3 : NF NCx (((I `Fn` I) `Fn` (I `Fn` I)) `Fn` ((I `Fn` I) `Fn` (I `Fn` I)))
try3 = normByEval (lambda' $ \x => x)

try4 : NF NCx ((I `Fn` I) `Fn` (I `Fn` I))
try4 = normByEval (App (App church2 church2) church2)

-- ex 2.11
-- TODO

-- ex 2.12 
-- TODO