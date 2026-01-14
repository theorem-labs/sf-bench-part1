/-
  Lean translation for in_not_nil_42_take2 and all dependencies
  
  The theorem states: forall l : list nat, In 42 l -> l <> []
  
  Required definitions:
  - nat
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Logic.LF.Logic.In
  - Original.False (for negation in the conclusion)
  - Logic.not (l <> [] means l = [] -> False)
  - Corelib.Init.Logic.eq
-/

set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- False proposition (for negation)
inductive Original_False : Prop where

-- Logic.not = fun P => P -> False  
def Logic_not (P : Prop) : Prop := P → Original_False

-- True proposition
inductive TrueProp : Prop where
  | I : TrueProp

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Equality in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (needed for the checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- Define 42 using nat constructors
def forty_two : nat := 
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))

-- The main theorem: in_not_nil_42_take2 is Admitted in Original.v
-- Lemma in_not_nil_42_take2 : forall l : list nat, In 42 l -> l <> [].
-- This unfolds to: forall l : list nat, In 42 l -> l = [] -> False
axiom Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take2 : 
  ∀ (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    Original_LF__DOT__Logic_LF_Logic_In forty_two l →
    Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_nil nat) →
    Original_False
