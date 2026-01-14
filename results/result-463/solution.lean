-- Lean 4 translation for zero_or_succ and its dependencies

set_option autoImplicit false

-- True in Prop (will become SProp in Rocq)
inductive PTrue : Prop where
  | intro : PTrue

def PTrue_intro : PTrue := PTrue.intro

-- Equality in Prop for Type arguments (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Equality in Prop for Prop arguments (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Define Nat_pred to match Rocq's Nat.pred
def Nat_pred : nat -> nat
  | nat.O => nat.O
  | nat.S n => n

-- or as a structure with an eliminator field for SProp-compatible elimination
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- The zero_or_succ theorem is Admitted in Original.v, so we declare it as an axiom
-- Original: forall n : nat, n = 0 \/ n = S (pred n)
axiom Original_LF__DOT__Logic_LF_Logic_zero__or__succ : 
  forall (n : nat), or (Corelib_Init_Logic_eq n _0) (Corelib_Init_Logic_eq n (S (Nat_pred n)))
