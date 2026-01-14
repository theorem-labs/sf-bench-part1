-- Lean 4 translation for plus_1_neq_0 and its dependencies

set_option autoImplicit false

-- True in Prop (will become SProp in Rocq)
-- Use MyTrue to avoid conflict with Lean's True
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- The plus_1_neq_0 theorem is Admitted in Original.v, so axiom here
-- Statement: forall n, eqb (n + 1) 0 = false
axiom Original_LF__DOT__AltAuto_LF_AltAuto_plus__1__neq__0 :
  ∀ (n : nat), Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add n (S _0)) _0)
    Original_LF__DOT__Basics_LF_Basics_false
