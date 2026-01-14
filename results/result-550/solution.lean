-- Lean 4 translation for leb_correct and dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb function (less-or-equal boolean)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- le as a decidable relation (computational version for easier SProp handling)
def nat_le : nat → nat → Bool
  | nat.O, _ => true
  | nat.S _, nat.O => false
  | nat.S n, nat.S m => nat_le n m

-- le as Prop based on the boolean
def le (n m : nat) : Prop := nat_le n m = true

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (will be SProp -> SProp -> SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- We define our own True-like type to export
-- This will be exported and then renamed in Imported.out
inductive MyTrue : Prop where
  | intro : MyTrue

-- leb_correct is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_leb__correct :
  ∀ (n m : nat),
    le n m →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true
