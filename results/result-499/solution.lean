-- Lean translation of Rocq definitions for mul_eq_0_ternary

-- True in Prop (will be imported as SProp in Rocq)
inductive MyTrue : Prop where
  | intro : MyTrue

def True_intro : MyTrue := MyTrue.intro

-- Equality in Prop (will be imported as SProp in Rocq)
inductive Corelib_Init_Logic_eq (A : Type) : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq A a a

def Corelib_Init_Logic_eq_refl (A : Type) (a : A) : Corelib_Init_Logic_eq A a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality on Prop (for SProp → SProp → SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop (A : Prop) : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop A a a

def Corelib_Init_Logic_eq_Prop_refl (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop A a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat (helper for multiplication)
def Nat_add : nat → nat → nat
  | nat.O, n => n
  | nat.S m, n => nat.S (Nat_add m n)

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, n => Nat_add (Nat_mul m n) n

-- and as a structure so it becomes a record with primitive projections
structure and (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

def and_intro (A B : Prop) (a : A) (b : B) : and A B := ⟨a, b⟩
def fst0 (A B : Prop) (p : and A B) : A := p.fst
def snd0 (A B : Prop) (p : and A B) : B := p.snd

-- or as a structure with an eliminator field
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_intro (A B : Prop) (e : ∀ C : Prop, (A → C) → (B → C) → C) : or A B := ⟨e⟩
def or.inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or.inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩
def elim (A B : Prop) (p : or A B) (C : Prop) (f : A → C) (g : B → C) : C := p.elim C f g

-- iff defined in terms of and
def iff (A B : Prop) : Prop := and (A → B) (B → A)

-- The main theorem is admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_mul__eq__0__ternary : 
  ∀ (n m p : nat), iff (Corelib_Init_Logic_eq nat (Nat_mul (Nat_mul n m) p) _0) 
                       (or (Corelib_Init_Logic_eq nat n _0) 
                           (or (Corelib_Init_Logic_eq nat m _0) 
                               (Corelib_Init_Logic_eq nat p _0)))
