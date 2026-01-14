-- Lean 4 translation for exists_example_2 and its dependencies

set_option autoImplicit false

-- True in Prop (use unusual name to avoid conflict with Lean's True)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality in Prop for SProp types (when applied to Prop-valued arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition for nat (to match Rocq's Nat.add)
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Existential quantifier in Prop (becomes SProp when imported)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- The exists_example_2 theorem is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_exists__example__2 :
  ∀ (x : nat),
    ex (fun H : nat => Corelib_Init_Logic_eq x (Nat_add (S (S (S (S _0)))) H)) →
    ex (fun H : nat => Corelib_Init_Logic_eq x (Nat_add (S (S _0)) H))
