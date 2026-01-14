-- Lean translation for silly_presburger_example
-- The original Rocq theorem is:
-- Example silly_presburger_example : forall m n o p,
--   m + n <= n + o /\ o + 3 = p + 3 ->
--   m <= p.
-- Admitted.

-- Basic types needed

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Use a namespace to avoid conflict with stdlib True
namespace MyDefs
def True : Prop := PTrue
end MyDefs

-- Equality in Prop (will be mapped to SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def PeanoNat_Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (PeanoNat_Nat_add n m)

-- Less-than-or-equal in Prop
inductive le : nat → nat → Prop where
  | le_n : (n : nat) → le n n
  | le_S : (n m : nat) → le n m → le n (nat.S m)

-- Conjunction in Prop
inductive and (A B : Prop) : Prop where
  | conj : A → B → and A B

-- The main axiom (silly_presburger_example is Admitted in Rocq)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_silly__presburger__example :
  ∀ (x x0 x1 x2 : nat),
    and (le (PeanoNat_Nat_add x x0) (PeanoNat_Nat_add x0 x1))
        (Corelib_Init_Logic_eq (PeanoNat_Nat_add x1 (S (S (S _0)))) (PeanoNat_Nat_add x2 (S (S (S _0))))) →
    le x x2
