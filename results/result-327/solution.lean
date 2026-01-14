-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Double function
def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- Custom Eq type for the existential (renamed to avoid conflict)
inductive MyEq (A : Type) : A → A → Prop where
  | refl : (x : A) → MyEq A x x

-- Existential quantifier (specialized to nat -> Prop)
inductive Original_LF__DOT__Logic_LF_Logic_Even_ex (P : nat → Prop) : Prop where
  | intro : (x : nat) → P x → Original_LF__DOT__Logic_LF_Logic_Even_ex P

-- Even definition: exists n, x = double n
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  Original_LF__DOT__Logic_LF_Logic_Even_ex (fun n => MyEq nat x (Original_LF__DOT__Induction_LF_Induction_double n))

-- four_is_Even is Admitted in the original, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_four__is__Even : Original_LF__DOT__Logic_LF_Logic_Even (S (S (S (S _0))))
