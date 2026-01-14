-- Lean 4 translation for silly_fact_2 and its dependencies

set_option autoImplicit false

-- Define nat as an inductive type to match Rocq's nat  
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- Define _0 and S
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Define Nat_add to match Rocq's Nat.add
def Nat_add : nat -> nat -> nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- True proposition (in SProp format for Rocq)
inductive PTrue : Prop where
  | intro : PTrue

-- Alias for True (named to avoid conflict with Lean's True)
def True' : Prop := PTrue

-- Equality (in Prop to match Rocq) - specialized to Type
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality for Prop  
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A -> Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- bar function: match x with | O => 5 | S _ => 5 end
-- Note: 5 = S (S (S (S (S O))))
def five : nat := nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))

def Original_LF__DOT__Tactics_LF_Tactics_bar : nat -> nat
  | nat.O => five
  | nat.S _ => five

-- silly_fact_2 is Admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_silly__fact__2 : 
  forall (m : nat), 
    Corelib_Init_Logic_eq 
      (Nat_add (Original_LF__DOT__Tactics_LF_Tactics_bar m) (nat.S nat.O))
      (Nat_add (Original_LF__DOT__Tactics_LF_Tactics_bar (Nat_add m (nat.S nat.O))) (nat.S nat.O))
