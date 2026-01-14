-- True in Prop (will become SProp in Rocq)
-- We need to export with a name that doesn't clash with Lean's True
-- Use a namespace to allow the name "True"
namespace Exported

inductive True : Prop where
  | intro : True

def True_intro : True := True.intro

end Exported

-- Equality in Prop (will become SProp in Rocq)
-- This mirrors the standard Eq but in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (will be SProp -> SProp -> SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat.add
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Nat_add n' m)

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- The plus_eqb_example theorem (admitted in Original.v, so axiom here)
-- Statement: forall n m p, (n =? m) = true -> (n + p =? m + p) = true
axiom Original_LF__DOT__Logic_LF_Logic_plus__eqb__example :
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb n m) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add n p) (Nat_add m p)) Original_LF__DOT__Basics_LF_Basics_true
