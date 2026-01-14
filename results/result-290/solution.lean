-- Lean 4 translation for square_mult and its dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Define Nat_mul to match Rocq's Nat.mul
def Nat_mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Alias for True in a namespace to avoid conflict with builtin True
namespace MyDefs
  def True : Prop := PTrue
end MyDefs

-- Define equality in Prop (becomes SProp when imported) - for Type
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Define equality for Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- Define square: n * n
def Original_LF__DOT__Tactics_LF_Tactics_square (n : nat) : nat :=
  Nat_mul n n

-- The main theorem - square_mult is Admitted in Original.v
-- square (n * m) = square n * square m
axiom Original_LF__DOT__Tactics_LF_Tactics_square__mult :
  forall (n m : nat),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Tactics_LF_Tactics_square (Nat_mul n m))
      (Nat_mul (Original_LF__DOT__Tactics_LF_Tactics_square n) (Original_LF__DOT__Tactics_LF_Tactics_square m))
