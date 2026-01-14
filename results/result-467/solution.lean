-- Lean 4 translation for test_doit3times and dependencies

set_option autoImplicit false

-- True in Prop (alias as PTrue for Rocq import, to avoid conflict with Lean's True)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Type (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality in Prop (for SProp -> SProp equality)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- minustwo function
def Original_LF__DOT__Basics_LF_Basics_minustwo : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n') => n'

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- test_doit3times is Admitted in Original.v, so we declare it as an axiom
-- test_doit3times: doit3times minustwo 9 = 3
axiom Original_LF__DOT__Poly_LF_Poly_test__doit3times : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_doit3times nat Original_LF__DOT__Basics_LF_Basics_minustwo 
      (S (S (S (S (S (S (S (S (S _0))))))))))  -- 9
    (S (S (S _0)))  -- 3
