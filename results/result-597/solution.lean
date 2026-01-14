-- Lean 4 translation for ev_inversion and all dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (becomes SProp when imported) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (also becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- And as a structure
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Or as a structure with eliminator
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Existential quantifier in Prop
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- ev inductive type from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n -> Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev_inversion: forall n, ev n -> n = 0 \/ exists n', n = S (S n') /\ ev n'
-- This is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__inversion :
  ∀ (x : nat),
    Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev x →
    or (Corelib_Init_Logic_eq x _0)
       (ex (fun H : nat => and (Corelib_Init_Logic_eq x (S (S H))) (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev H)))
