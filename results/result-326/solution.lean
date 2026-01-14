-- Lean 4 translation for even_1000 and dependencies

-- nat type
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- double function
def Original_LF__DOT__Induction_LF_Induction_double : nat -> nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- Custom Eq type for the existential (renamed to avoid conflict)
inductive MyEq (A : Type) : A -> A -> Prop where
  | refl : (x : A) -> MyEq A x x

-- Existential quantifier (specialized to nat -> Prop)
inductive Original_LF__DOT__Logic_LF_Logic_Even_ex (P : nat -> Prop) : Prop where
  | intro : (x : nat) -> P x -> Original_LF__DOT__Logic_LF_Logic_Even_ex P

-- Even definition: exists n, x = double n
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  Original_LF__DOT__Logic_LF_Logic_Even_ex (fun n => MyEq nat x (Original_LF__DOT__Induction_LF_Induction_double n))

-- Build 1000 manually using S
-- 1000 = S^1000(0)
-- We use S^10 helper and compose
def S10 (n : nat) : nat := S (S (S (S (S (S (S (S (S (S n)))))))))
def S100 (n : nat) : nat := S10 (S10 (S10 (S10 (S10 (S10 (S10 (S10 (S10 (S10 n)))))))))
def n1000 : nat := S100 (S100 (S100 (S100 (S100 (S100 (S100 (S100 (S100 (S100 _0)))))))))

-- even_1000 is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_even__1000 : Original_LF__DOT__Logic_LF_Logic_Even n1000
