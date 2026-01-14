-- Lean 4 translation for add_assoc'' and its dependencies

set_option autoImplicit false

-- nat type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- True to match Rocq's True (lives in Prop for SProp in Rocq)
-- We use an alias to Lean's builtin True
def True' := _root_.True

-- Equality type to match Rocq's eq (in SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- add_assoc'' is Admitted in Original.v, so we use an axiom (sorry) 
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc'' : 
  forall (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)
