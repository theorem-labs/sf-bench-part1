-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- le as an inductive type matching Rocq's le
inductive le : nat -> nat -> Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (nat.S m)

-- lt as le (S n) m (matching Rocq)
def lt (n m : nat) : Prop := le (nat.S n) m

-- ge as le n m (i.e., ge m n = n <= m)
def ge (m n : nat) : Prop := le n m

-- or as a structure with an eliminator field
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or.inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or.inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- The main theorem we need (admitted in Original.v, so we declare it as an axiom)
axiom Original_LF__DOT__IndProp_LF_IndProp_lt__ge__cases : 
  ∀ (n m : nat), or (lt n m) (ge n m)
