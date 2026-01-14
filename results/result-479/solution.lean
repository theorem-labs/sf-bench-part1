-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality for Prop (which maps to SProp in Rocq)
inductive eq'_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : eq'_Prop a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop x y

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

-- fold definition: folds a function over a list
def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X) (b : Y) : Y :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => b
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

-- length definition: computes length of a list
def Original_LF__DOT__Poly_LF_Poly_length {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : nat :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length t)

-- fold_length definition: computes length using fold
def Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : nat :=
  Original_LF__DOT__Poly_LF_Poly_fold (fun _ n => nat.S n) l nat.O

-- fold_length_correct: fold_length l = length l
-- This is Admitted in Rocq, so we axiomatize it
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length__correct :
  ∀ (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X),
    Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_Exercises_fold__length l) (Original_LF__DOT__Poly_LF_Poly_length l)
