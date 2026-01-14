/-
  Lean translation for lemma_application_ex and all dependencies
  
  The theorem states: forall n ns, In n (map (fun m => m * 0) ns) -> n = 0
  
  Required definitions:
  - nat, S, 0
  - Original.LF_DOT_Poly.LF.Poly.list
  - Original.LF_DOT_Poly.LF.Poly.nil
  - Original.LF_DOT_Poly.LF.Poly.cons
  - Original.LF_DOT_Poly.LF.Poly.map
  - Original.LF_DOT_Logic.LF.Logic.In
  - Corelib.Init.Logic.eq
  - Nat.mul
  - True
  - False
-/

set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True proposition (named True_ to avoid clash with Lean's True, but exported as True)
inductive True_ : Prop where
  | I : True_

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

-- map function
def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | .nil => .nil
  | .cons h t => .cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

-- Equality in Prop
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (needed for the checker)
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

-- The main theorem: lemma_application_ex is Admitted in Original.v
-- Example lemma_application_ex : forall n ns, In n (map (fun m => m * 0) ns) -> n = 0.
axiom Original_LF__DOT__Logic_LF_Logic_lemma__application__ex : 
  ∀ (n : nat) (ns : Original_LF__DOT__Poly_LF_Poly_list nat),
    Original_LF__DOT__Logic_LF_Logic_In n (Original_LF__DOT__Poly_LF_Poly_map (fun m : nat => Nat_mul m _0) ns) →
    Corelib_Init_Logic_eq n _0
