-- True in Prop (will become SProp in Rocq)
-- Use a namespace to avoid collision with Lean's True
namespace Imported

inductive True : Prop where
  | intro : True

end Imported

-- Equality in Prop (will become SProp in Rocq)
-- This mirrors the standard Eq but in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Helper to build nat from Nat
def natOfNat : Nat → nat
  | 0 => nat.O
  | Nat.succ n => nat.S (natOfNat n)

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- even function (matching LF.Basics.even)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- The not_even_1001 theorem (admitted in Original.v, so axiom here)
-- It states: even 1001 = false
axiom Original_LF__DOT__Logic_LF_Logic_not__even__1001 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_even (natOfNat 1001))
    Original_LF__DOT__Basics_LF_Basics_false
