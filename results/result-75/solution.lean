prelude
/-
  Lean translation for auto_example_6'
  
  The original Rocq theorem is:
  Example auto_example_6' : forall n m p : nat,
    (n <= p -> (n <= m /\ m <= n)) ->
    n <= p ->
    n = m.
  Admitted.
-/

-- We define our own versions to ensure proper exports
-- Names must match what the Rocq checker expects: Imported.nat, Imported.True, etc.

-- Basic types needed
universe u

-- Natural numbers
inductive nat : Type where
  | zero : nat
  | succ : nat → nat

-- True (unit type as SProp equivalent)
inductive True : Prop where
  | intro : True

-- Equality (in Prop, will be mapped to SProp)
inductive Corelib_Init_Logic_eq {α : Type} : α → α → Prop where
  | refl : (a : α) → Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {α : Type} (a : α) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Less-than-or-equal (in Prop, will be mapped to SProp)
inductive le : nat → nat → Prop where
  | le_n : (n : nat) → le n n
  | le_S : (n m : nat) → le n m → le n (nat.succ m)

-- Conjunction (in Prop, will be mapped to SProp)
inductive and (A B : Prop) : Prop where
  | conj : A → B → and A B

-- conj constructor alias for export
def conj {A B : Prop} (a : A) (b : B) : and A B := and.conj a b

-- The main axiom (auto_example_6' is Admitted in Rocq)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6' :
  ∀ (x x0 x1 : nat),
    (le x x1 → and (le x x0) (le x0 x)) →
    le x x1 →
    Corelib_Init_Logic_eq x x0
