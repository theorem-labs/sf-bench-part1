/-
  Lean translation for In_example_2 and all dependencies
  
  The theorem states: forall n, In n [2; 4] -> exists n', n = 2 * n'
  
  Required definitions:
  - nat, S, 0
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Poly.LF.Poly.cons
  - Original.LF_DOT_Logic.LF.Logic.In
  - Corelib.Init.Logic.eq
  - Nat.mul
  - ex
  - True
-/

set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True proposition
inductive TrueProp : Prop where
  | I : TrueProp

-- False proposition
inductive Original_False : Prop where

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Equality in Prop
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Nat addition
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Nat multiplication
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- Existential quantifier in Prop
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- The main theorem: In_example_2 is Admitted in Original.v
-- Example In_example_2 : forall n, In n [2; 4] -> exists n', n = 2 * n'.
-- The list [2; 4] = cons 2 (cons 4 nil)
-- 2 = S (S O), 4 = S (S (S (S O)))
axiom Original_LF__DOT__Logic_LF_Logic_In__example__2 : 
  ∀ (x : nat),
    Original_LF__DOT__Logic_LF_Logic_In x 
      (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0)) 
        (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) 
          (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
    ex (fun H : nat => Corelib_Init_Logic_eq x (Nat_mul (S (S _0)) H))
