-- Lean 4 translation for auto_example_7' and all dependencies
set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Define 42 as a nat (42 = S^42(0))
def nat_42 : nat := S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))

-- Boolean for le
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

-- Equality type (will become SProp Eq in Rocq)
inductive RocqEq {A : Type} : A → A → Prop where
  | refl (a : A) : RocqEq a a

def RocqEq_refl {A : Type} (a : A) : RocqEq a a := RocqEq.refl a

-- nat_le for comparison
def nat_le : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_le n m

-- le as Prop based on boolean
def le (n m : nat) : Prop := RocqEq (nat_le n m) RocqBool.true

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- is_fortytwo definition
def Original_LF__DOT__Auto_LF_Auto_is__fortytwo (x : nat) : Prop := RocqEq x nat_42

-- auto_example_7': Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__7' :
  ∀ (x : nat), and (le x nat_42) (le nat_42 x) → Original_LF__DOT__Auto_LF_Auto_is__fortytwo x
