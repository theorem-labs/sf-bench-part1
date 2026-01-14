-- Lean 4 translation for cms and all its dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- even function (from LF.Basics)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- div2 function (from LF.IndProp)
def Original_LF__DOT__IndProp_LF_IndProp_div2 : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n) => nat.S (Original_LF__DOT__IndProp_LF_IndProp_div2 n)

-- Addition for nat (needed for csf)
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (nat_add n' m)

-- Multiplication for nat (needed for csf: 3 * n)
def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => nat_add m (nat_mul n' m)

-- csf function (from LF.IndProp)
def Original_LF__DOT__IndProp_LF_IndProp_csf (n : nat) : nat :=
  match Original_LF__DOT__Basics_LF_Basics_even n with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__IndProp_LF_IndProp_div2 n
  | Original_LF__DOT__Basics_LF_Basics_bool.false => nat_add (nat_mul (nat.S (nat.S (nat.S nat.O))) n) (nat.S nat.O)

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- cs relation (from LF.IndProp)
-- Rocq: Definition cs (n m : nat) : Prop := csf n = m.
def Original_LF__DOT__IndProp_LF_IndProp_cs (n m : nat) : Prop :=
  Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_csf n) m

-- clos_refl_trans (from LF.IndProp)
-- Rocq:
-- Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
--   | rt_step (x y : X) : R x y -> clos_refl_trans R x y
--   | rt_refl (x : X) : clos_refl_trans R x x
--   | rt_trans (x y z : X) : clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.
inductive Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step : ∀ x y, R x y → Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y
  | rt_refl : ∀ x, Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x x
  | rt_trans : ∀ x y z, Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y →
                        Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R y z →
                        Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x z

-- cms (from LF.IndProp)
-- Rocq: Definition cms n m := clos_refl_trans cs n m.
def Original_LF__DOT__IndProp_LF_IndProp_cms (n m : nat) : Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans Original_LF__DOT__IndProp_LF_IndProp_cs n m
