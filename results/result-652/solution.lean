-- Lean 4 translation for combine_odd_even_elim_odd and dependencies
set_option linter.all false

-- True in Prop (will become SProp in Rocq)
-- Use RocqTrue since True is a builtin name in Lean
-- We'll rename it manually in the exported .out file
inductive RocqTrue : Prop where
  | intro : RocqTrue

def RocqTrue_intro : RocqTrue := RocqTrue.intro

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (also becomes SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- S as a separate definition (for easier export)
def S : nat → nat := nat.S
def _0 : nat := nat.O

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function = negb (even n)
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- combine_odd_even is admitted in original, so it's an axiom
axiom Original_LF__DOT__Logic_LF_Logic_combine__odd__even : (nat → Prop) → (nat → Prop) → nat → Prop

-- combine_odd_even_elim_odd is also admitted in original, so it's an axiom
axiom Original_LF__DOT__Logic_LF_Logic_combine__odd__even__elim__odd :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    Original_LF__DOT__Logic_LF_Logic_combine__odd__even Podd Peven n →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_odd n) Original_LF__DOT__Basics_LF_Basics_true →
    Podd n
