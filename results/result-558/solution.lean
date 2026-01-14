-- Lean translation for LF.Poly definitions

-- True in Prop (will become SProp in Rocq)
-- Using MyTrue to avoid conflict with Lean's built-in True
inductive MyTrue : Prop where
  | I : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Equality for Prop (will become SProp in Rocq)
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

-- app function
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- rev function
def Original_LF__DOT__Poly_LF_Poly_rev {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_app (Original_LF__DOT__Poly_LF_Poly_rev t) 
        (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- rev_exercise1: forall l l' : list nat, l = rev l' -> l' = rev l
-- This is an Admitted theorem in Original.v, so we axiomatize it
axiom Original_LF__DOT__Tactics_LF_Tactics_rev__exercise1 :
  ∀ (l l' : Original_LF__DOT__Poly_LF_Poly_list nat),
    Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_rev l') →
    Corelib_Init_Logic_eq l' (Original_LF__DOT__Poly_LF_Poly_rev l)
