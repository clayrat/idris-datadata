module ArityGen.Ch3

%default total
%access public export

-- 3.1 Universe definition

data Kind : Type where
    Base : Kind
    Fun : Kind -> Kind -> Kind
  
IntKind : Kind -> Type 
IntKind  Base     = Type
IntKind (Fun a b) = IntKind a -> IntKind b

data Const : Kind -> Type where
  N : Const Base
  U : Const Base
  Sum : Const (Base `Fun` (Base `Fun` Base))
  Prod : Const (Base `Fun` (Base `Fun` Base))
  
IntCst : Const k -> IntKind k
IntCst N    = Nat
IntCst U    = Unit
IntCst Sum  = Either
IntCst Prod = Pair

Ctx : Type
Ctx = List Kind

data TyVar : Ctx -> Kind -> Type where
  VZ : TyVar (k :: g) k
  VS : TyVar g k -> TyVar (k' :: g) k

data Typ : Ctx -> Kind -> Type where
  Var : TyVar g k -> Typ g k
  Lam : Typ (k1 :: g) k2 -> Typ g (k1 `Fun` k2)
  App : Typ g (k1 `Fun` k2) -> Typ g k1 -> Typ g k2
  Con : Const k -> Typ g k

Ty : Kind -> Type
Ty = Typ []

data Env : List Kind -> Type where
  Nil : Env []
  (::) : IntKind k -> Env g -> Env (k :: g)

sLookup : TyVar g k -> Env g -> IntKind k
sLookup  VZ    (v :: g) = v
sLookup (VS x) (v :: g) = sLookup x g

interp : Typ g k -> Env g -> IntKind k
interp (Var x)   e = sLookup x e
interp (Lam l)   e = \y => interp l (y :: e)
interp (App s t) e = (interp s e) (interp t e)
interp (Con c)   e = IntCst c
      
int : Ty k -> IntKind k
int t = interp t []

Option : Type -> Type
Option = \a => Either () a

OptionTy : Ty (Base `Fun` Base)
OptionTy = Lam (App (App (Con Sum) (Con U)) (Var VZ))

test : Option = int OptionTy
test = Refl