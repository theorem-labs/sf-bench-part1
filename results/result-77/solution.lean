-- Lean 4 translation for Collatz_holds_for_12 and all dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- even function (from LF.Basics)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- div2 function (from LF.IndProp)
def Original_LF__DOT__IndProp_LF_IndProp_div2 : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n) => nat.S (Original_LF__DOT__IndProp_LF_IndProp_div2 n)

-- Addition for nat
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (nat_add n' m)

-- Multiplication for nat
def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => nat_add m (nat_mul n' m)

-- Standard Coq equality (will be imported to SProp)
inductive Corelib_Init_Logic_eq {A : Sort u} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Collatz_holds_for inductive type
inductive Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for : nat → Prop where
  | Chf_one : Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for (nat.S nat.O)
  | Chf_even (n : nat) : 
      Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_true →
      Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for (Original_LF__DOT__IndProp_LF_IndProp_div2 n) →
      Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for n
  | Chf_odd (n : nat) :
      Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_false →
      Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for (nat_add (nat_mul (nat.S (nat.S (nat.S nat.O))) n) (nat.S nat.O)) →
      Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for n

-- Collatz_holds_for_12 is admitted in the original, so we use axiom/sorry
axiom Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 :
  Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for 
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))
