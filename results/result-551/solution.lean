/-
  Lean translation for le_inversion and all its dependencies
  
  Original Rocq definition:
    Theorem le_inversion : forall (n m : nat),
      le n m ->
      (n = m) \/ (exists m', m = S m' /\ le n m').
    Proof.
      Admitted.
-/

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- True in Prop (will be imported as Imported.PTrue)
-- We also need Imported.True, so we'll use a workaround
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (becomes SProp when imported) - for Type
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- or with an elimination field for SProp-compatible elimination
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- Existential quantifier in Prop (becomes SProp when imported)
inductive ex {A : Type} (P : A -> Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- Define le as an inductive proposition (from LePlayground module)
inductive Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le : nat → nat → Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m → Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n (nat.S m)

-- The main axiom: le_inversion (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_le__inversion :
  ∀ (n m : nat),
    Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m →
    or (Corelib_Init_Logic_eq n m)
       (ex (fun m' : nat => and (Corelib_Init_Logic_eq m (S m')) (Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le n m')))
