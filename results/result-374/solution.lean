-- Lean 4 translation for restricted_excluded_middle_eq and all dependencies
set_option autoImplicit false

-- We define our own True/False with names that avoid Lean's builtin names

inductive RocqTrue : Prop where
  | intro : RocqTrue

def RocqTrue_intro : RocqTrue := RocqTrue.intro

inductive RocqFalse : Prop where

noncomputable def RocqFalse_recl (C : Type) (h : RocqFalse) : C := nomatch h
noncomputable def RocqFalse_indl (C : RocqFalse → Prop) (h : RocqFalse) : C h := nomatch h

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- Equality for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

def Corelib_Init_Logic_eq_recl {A : Type} (a : A) (C : A → Type) (h : C a) (b : A)
  (H : Corelib_Init_Logic_eq a b) : C b :=
  match H with
  | Corelib_Init_Logic_eq.refl _ => h

-- Equality for Prop arguments (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

noncomputable def Corelib_Init_Logic_eq_Prop_recl {A : Prop} (a : A) (C : A → Type) (h : C a) (b : A)
  (H : Corelib_Init_Logic_eq_Prop a b) : C b :=
  Corelib_Init_Logic_eq_Prop.rec (motive := fun x _ => C x) h H

noncomputable def Corelib_Init_Logic_eq_Prop_indl {A : Prop} (a : A) (C : A → Prop) (h : C a) (b : A)
  (H : Corelib_Init_Logic_eq_Prop a b) : C b :=
  Corelib_Init_Logic_eq_Prop.rec (motive := fun x _ => C x) h H

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O : nat := nat.O
def nat_S : nat → nat := nat.S

-- or as a structure with an eliminator field for SProp-compatible elimination
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- The main axiom: restricted_excluded_middle_eq (admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle__eq :
  ∀ (n m : nat), or (Corelib_Init_Logic_eq n m) (Corelib_Init_Logic_eq n m → RocqFalse)
