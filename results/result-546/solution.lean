-- True in Prop (will become SProp in Rocq)
-- We alias the standard True
def True' := True
def True'_I : True' := True.intro

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Prop version of equality for SProp arguments (just uses True since all SProp inhabitants are equal)
def Corelib_Init_Logic_eq_Prop (A : Prop) (x y : A) : Prop := True'

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- The pair constructor
def Original_LF__DOT__Poly_LF_Poly_pair {X Y : Type} (x : X) (y : Y) : Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Original_LF__DOT__Poly_LF_Poly_prod.pair x y

-- silly2a is admitted in Rocq, so we axiomatize it
axiom Original_LF__DOT__Tactics_LF_Tactics_silly2a : 
  forall (n m : nat),
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_pair n n) (Original_LF__DOT__Poly_LF_Poly_pair m m) →
  (forall (q r : nat), 
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_pair q q) (Original_LF__DOT__Poly_LF_Poly_pair r r) → 
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_cons q (Original_LF__DOT__Poly_LF_Poly_nil nat)) 
                          (Original_LF__DOT__Poly_LF_Poly_cons r (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_cons n (Original_LF__DOT__Poly_LF_Poly_nil nat)) 
                        (Original_LF__DOT__Poly_LF_Poly_cons m (Original_LF__DOT__Poly_LF_Poly_nil nat))
