-- Lean 4 translation for function_equality_ex1 and its dependencies

set_option autoImplicit false

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop for Type arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_pred to match Rocq's Nat.pred
def Nat_pred : nat -> nat
  | nat.O => nat.O
  | nat.S n => n

-- The function_equality_ex1 theorem is Admitted in Original.v, so we declare it as an axiom
-- Original: (fun x => 3 + x) = (fun x => (pred 4) + x)
axiom Original_LF__DOT__Logic_LF_Logic_function__equality__ex1 : 
  Corelib_Init_Logic_eq 
    (fun x : nat => Nat_add (nat.S (nat.S (nat.S nat.O))) x)
    (fun x : nat => Nat_add (Nat_pred (nat.S (nat.S (nat.S (nat.S nat.O))))) x)
