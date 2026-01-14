-- Lean 4 translation for silly2_fixed and its dependencies

set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Existential quantifier in Prop (becomes SProp when imported)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- The silly2_fixed theorem is Admitted in Original.v, so we declare it as an axiom
-- silly2_fixed : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
--   (exists y, P 42 y) -> (forall x y : nat, P x y -> Q x) -> Q 42.
axiom Original_LF__DOT__Auto_LF_Auto_silly2__fixed :
  ∀ (P : nat → nat → Prop) (Q : nat → Prop),
    ex (fun y : nat => P (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))) y) →
    (∀ x y : nat, P x y → Q x) →
    Q (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0))))))))))))))))))))))))))))))))))))))))))
