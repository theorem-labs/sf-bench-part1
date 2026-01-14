-- Use Lean's built-in Nat for natural numbers
-- Define aliases that match what checkers expect
def nat : Type := Nat
def S : Nat → Nat := Nat.succ
def O : Nat := 0
def _0 : Nat := 0  -- Alternate name expected by some checkers

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Empty inductive type for False - use Prop so it becomes SProp in Rocq
inductive Original_False : Prop where

-- Definition of not (negation)
def Original_LF__DOT__Logic_LF_Logic_not (P : Prop) : Prop := P → Original_False

-- nostutter is an empty inductive predicate (has no constructors)
-- In Rocq it's: Inductive nostutter {X:Type} : list X -> Prop := .
-- Use Prop so it becomes SProp in Rocq
inductive Original_LF__DOT__IndProp_LF_IndProp_nostutter {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Prop where

-- test_nostutter_4 is an Admitted axiom: not (nostutter [3;1;1;4])
-- not P = P -> False
-- So test_nostutter_4 : nostutter [3;1;1;4] -> False
axiom Original_LF__DOT__IndProp_LF_IndProp_test__nostutter__4 :
  Original_LF__DOT__IndProp_LF_IndProp_nostutter
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S O)))
       (Original_LF__DOT__Poly_LF_Poly_cons (S O)
          (Original_LF__DOT__Poly_LF_Poly_cons (S O)
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S O)))) (Original_LF__DOT__Poly_LF_Poly_nil Nat))))) →
  Original_False
