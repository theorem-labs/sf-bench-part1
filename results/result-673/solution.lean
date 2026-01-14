-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function (defined as negb (even n))
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- silly_ex axiom (admitted in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_silly__ex :
  ∀ (p : nat),
    (∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_true →
                  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even (S n)) Original_LF__DOT__Basics_LF_Basics_false) →
    (∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_false →
                  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_odd n) Original_LF__DOT__Basics_LF_Basics_true) →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even p) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_odd (S p)) Original_LF__DOT__Basics_LF_Basics_true
