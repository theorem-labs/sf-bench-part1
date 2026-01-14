/-!
  Lean translation for even_double_conv and its dependencies.
  
  We need to export:
  - nat (isomorphic to Rocq nat)
  - S (successor function)
  - True_ (for SProp True)
  - Corelib_Init_Logic_eq (isomorphic to Rocq equality in SProp)
  - Original_LF__DOT__Basics_LF_Basics_bool (boolean type)
  - Original_LF__DOT__Basics_LF_Basics_true/false (bool constructors)
  - Original_LF__DOT__Basics_LF_Basics_even (even function)
  - Original_LF__DOT__Basics_LF_Basics_bool__rec (bool recursor)
  - Original_LF__DOT__Induction_LF_Induction_double (the double function)
  - ex (existential type)
  - Original_LF__DOT__Logic_LF_Logic_even__double__conv (the theorem, as axiom since it's Admitted)
-/

-- Define our own nat to avoid issues with Lean's Nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def S : nat → nat := nat.S

-- We cannot define True in Lean, so we will manually edit the .out file
-- to rename True_ to True after export
inductive True_ : Prop where
  | intro : True_

-- Define equality in Prop (will be mapped to SProp in Rocq)
inductive Corelib_Init_Logic_eq {α : Type} (a : α) : α → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {α : Type} (a : α) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Prop version of equality (α : Prop)
inductive Corelib_Init_Logic_eq_Prop {α : Prop} (a : α) : α → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {α : Prop} (a : α) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl

-- Existential type in Prop
inductive ex {α : Type} (P : α → Prop) : Prop where
  | intro (w : α) (h : P w) : ex P

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- The recursor for bool
def Original_LF__DOT__Basics_LF_Basics_bool__rec {motive : Original_LF__DOT__Basics_LF_Basics_bool → Sort u}
  (htrue : motive Original_LF__DOT__Basics_LF_Basics_true)
  (hfalse : motive Original_LF__DOT__Basics_LF_Basics_false)
  (b : Original_LF__DOT__Basics_LF_Basics_bool) : motive b :=
  match b with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => htrue
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => hfalse

-- even function on nat (matching the Rocq definition)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_true
  | nat.S nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- double function on nat (matching the Rocq definition)
def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- The theorem even_double_conv as an axiom (it's Admitted in the original)
-- forall n, exists k, n = if even n then double k else S (double k)
axiom Original_LF__DOT__Logic_LF_Logic_even__double__conv :
  ∀ (n : nat),
    ex (fun k : nat =>
      Corelib_Init_Logic_eq n
        (Original_LF__DOT__Basics_LF_Basics_bool__rec (motive := fun _ : Original_LF__DOT__Basics_LF_Basics_bool => nat)
          (Original_LF__DOT__Induction_LF_Induction_double k)
          (nat.S (Original_LF__DOT__Induction_LF_Induction_double k))
          (Original_LF__DOT__Basics_LF_Basics_even n)))
