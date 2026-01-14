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

-- In predicate: checks if x is in the list
-- Rocq definition:
-- Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
--   match l with
--   | [] => False
--   | x' :: l' => x' = x \/ In x l'
--   end.
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- In10' : In 10 [1;2;3;4;5;6;7;8;9;10]
-- This is Admitted in the original, so we use an axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_In10' :
  Original_LF__DOT__Logic_LF_Logic_In
    (S (S (S (S (S (S (S (S (S (S O))))))))))  -- 10
    (Original_LF__DOT__Poly_LF_Poly_cons (S O)  -- 1
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S O))  -- 2
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S O)))  -- 3
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S O))))  -- 4
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S O)))))  -- 5
                   (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S O))))))  -- 6
                      (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S O)))))))  -- 7
                         (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S O))))))))  -- 8
                            (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S (S O)))))))))  -- 9
                               (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S (S (S O))))))))))  -- 10
                                  (Original_LF__DOT__Poly_LF_Poly_nil Nat)))))))))))
