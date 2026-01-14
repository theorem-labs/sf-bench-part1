-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def S : nat → nat := nat.S

-- Equality in Prop (which will become SProp in Rocq) - Type version
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl : ∀ (a : A), Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl : ∀ (a : A), Corelib_Init_Logic_eq_Prop a a

-- Use Lean's builtin True and give it an alias for export
def MyTrue : Prop := _root_.True

-- injective definition
def Original_LF__DOT__Logic_LF_Logic_injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, Corelib_Init_Logic_eq (f x) (f y) → Corelib_Init_Logic_eq x y

-- succ_inj is Admitted in Original.v, so we translate it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_succ__inj :
  ∀ x y : nat, Corelib_Init_Logic_eq (S x) (S y) → Corelib_Init_Logic_eq x y
