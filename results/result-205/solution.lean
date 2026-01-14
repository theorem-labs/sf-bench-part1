-- Lean 4 translation for AltAuto.auto_example_7' and all dependencies
set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Define 42 as a nat (42 = S^42(0))
def fortytwo : nat := S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))

-- Define le as an inductive (matching Coq's le)
inductive le : nat → nat → Prop where
  | le_n : ∀ n, le n n
  | le_S : ∀ n m, le n m → le n (nat.S m)

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- is_fortytwo definition for AltAuto module
-- This is defined as an inductive with a single constructor
inductive Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo : nat → Prop where
  | intro : Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo fortytwo

-- auto_example_7': Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__7' :
  ∀ (x : nat), and (le x fortytwo) (le fortytwo x) → Original_LF__DOT__AltAuto_LF_AltAuto_is__fortytwo x
