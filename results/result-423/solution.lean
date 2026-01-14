-- True in Prop (will be imported as SProp in Rocq)
def MyTrue : Prop := _root_.True

-- Equality in Prop for Type (will be imported as SProp in Rocq)
inductive Corelib_Init_Logic_eq (A : Type) : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq A a a

def Corelib_Init_Logic_eq_refl (A : Type) (a : A) : Corelib_Init_Logic_eq A a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop for Prop (will be imported as SProp in Rocq)
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

-- or as a structure with an eliminator field
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or.inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or.inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- The main theorem mult_is_O is admitted in Original.v, so we declare it as an axiom
-- mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0
axiom Original_LF__DOT__Logic_LF_Logic_mult__is__O : 
  ∀ (n m : nat), Corelib_Init_Logic_eq nat (Nat_mul n m) _0 → 
                  or (Corelib_Init_Logic_eq nat n _0) (Corelib_Init_Logic_eq nat m _0)
