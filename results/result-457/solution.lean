-- Lean 4 translation for test_plus3' and dependencies

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- plus function from LF.Basics (recursive)
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- plus3 = plus 3
def Original_LF__DOT__Poly_LF_Poly_plus3 : nat → nat :=
  Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O)))

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- test_plus3' is Admitted, so we axiomatize it
-- The statement is: doit3times plus3 0 = 9
axiom Original_LF__DOT__Poly_LF_Poly_test__plus3' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_doit3times nat Original_LF__DOT__Poly_LF_Poly_plus3 _0)
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
