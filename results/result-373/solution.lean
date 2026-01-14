-- Lean 4 translation for and_example2 and its dependencies

-- Define nat as an inductive type to match Rocq's nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Aliases for 0 and S
def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- True in Prop  
inductive PTrue : Prop where
  | intro : PTrue

-- Define equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq a a

-- Equality at Prop level (for SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A -> A -> Prop where
  | refl : (a : A) -> Corelib_Init_Logic_eq_Prop a a

-- Define and as a structure matching Rocq's and
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- The main theorem and_example2 is Admitted in Original.v, so we use an axiom here
-- forall n m : nat, n = 0 /\ m = 0 -> n + m = 0
axiom Original_LF__DOT__Logic_LF_Logic_and__example2 :
  forall (n m : nat),
    and (Corelib_Init_Logic_eq n _0) (Corelib_Init_Logic_eq m _0) ->
    Corelib_Init_Logic_eq (Nat_add n m) _0
