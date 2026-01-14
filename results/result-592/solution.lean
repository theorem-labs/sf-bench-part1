-- Lean 4 translation for plus_exists_leb and all dependencies

set_option autoImplicit false

-- True in Prop (will become SProp in Rocq)
abbrev MyTrue : Prop := _root_.True

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (will become SProp -> SProp -> SProp in Rocq)
-- This is used when the first argument is in Prop/SProp
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O : nat := nat.O
def nat_S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- leb function (less than or equal for booleans)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- Existential in Prop
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- The plus_exists_leb theorem is Admitted in Original.v, so we declare it as an axiom
-- Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
axiom Original_LF__DOT__Logic_LF_Logic_plus__exists__leb :
  ∀ (n m : nat),
    ex (fun x => Corelib_Init_Logic_eq m (Nat_add n x)) →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true
