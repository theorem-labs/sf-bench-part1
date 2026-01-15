-- Unified Solution.lean merging all required definitions

set_option autoImplicit false

-- ============ Basic Types ============

-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality over Prop (for SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type in Prop (will be imported as SProp in Rocq)
inductive True_ : Prop where
  | intro : True_

-- False (empty type in Prop) - renamed to avoid Lean's False
inductive RocqFalse : Prop where

-- Alias for export  
def False_ : Prop := RocqFalse

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- ============ Bool Type (LF.Basics) ============

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

-- odd function
def Original_LF__DOT__Basics_LF_Basics_odd : nat → Original_LF__DOT__Basics_LF_Basics_bool :=
  fun n => Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- ============ Letter, Modifier, Grade Types (LF.Basics) ============

-- Letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.F

-- Modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- Grade type
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- lower_grade is an axiom (Admitted) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- lower_grade_F_Minus is an axiom (Admitted theorem) in the original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade__F__Minus :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_lower__grade
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Minus))
    (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_F Original_LF__DOT__Basics_LF_Basics_Minus)

-- ============ Polymorphic List (LF.Poly) ============

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- length function
def Original_LF__DOT__Poly_LF_Poly_length {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ l' => nat.S (Original_LF__DOT__Poly_LF_Poly_length l')

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- test_length1: length [1; 2; 3] = 3 (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_test__length1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_length
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
    (S (S (S _0)))

-- test_filter1: filter even [1;2;3;4] = [2;4] (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_test__filter1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter Original_LF__DOT__Basics_LF_Basics_even
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0)))
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))

-- ============ NatList (LF.Lists.NatList) ============

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is a type alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- count is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_all is admitted (axiom) in the original Rocq code
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- test_count2: count 6 [1;2;3;1;4;1] = 0 (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__count2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count
       (S (S (S (S (S (S _0))))))  -- 6
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))  -- 3
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))))  -- 1
    _0  -- 0

-- test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0 (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count
       (S (S (S (S (S _0)))))  -- 5
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all
          (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))  -- 2
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))  -- 4
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)  -- 1
                      Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
    _0  -- 0

-- ============ Logic Types ============

-- Logic.not (negation)
def Logic_not (P : Prop) : Prop := P → False_

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- ============ le and lt ============

-- Define le as a decidable relation using a recursive boolean function
def nat_le : nat → nat → Bool
  | nat.O, _ => true
  | nat.S _, nat.O => false
  | nat.S n, nat.S m => nat_le n m

-- Define le as a Prop based on the boolean
def le (n m : nat) : Prop := nat_le n m = true

-- Define lt as S n <= m (matching Rocq's definition)
def lt (n m : nat) : Prop := le (nat.S n) m

-- le_step axiom: forall n m p, n < m -> m <= S p -> n <= p (Admitted in Original.v)
axiom Original_LF_Rel_le__step : ∀ (n m p : nat), lt n m → le m (nat.S p) → le n p

-- ============ nor (LF.AltAuto) ============

inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- nor_comm': nor P Q <-> nor Q P (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' :
  ∀ (P Q : Prop), iff (Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q) (Original_LF__DOT__AltAuto_LF_AltAuto_nor Q P)

-- ============ injective and succ_inj (LF.Logic) ============

def Original_LF__DOT__Logic_LF_Logic_injective {A B : Type} (f : A → B) : Prop :=
  ∀ x y : A, Corelib_Init_Logic_eq (f x) (f y) → Corelib_Init_Logic_eq x y

-- succ_inj is Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_succ__inj :
  ∀ x y : nat, Corelib_Init_Logic_eq (S x) (S y) → Corelib_Init_Logic_eq x y

-- ============ forallb and All (LF.Logic) ============

-- forallb is Admitted in Rocq
axiom Original_LF__DOT__Logic_LF_Logic_forallb :
  {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- All is Admitted in Rocq
axiom Original_LF__DOT__Logic_LF_Logic_All :
  {T : Type} → (T → Prop) → Original_LF__DOT__Poly_LF_Poly_list T → Prop

-- forallb_true_iff is Admitted in Rocq
axiom Original_LF__DOT__Logic_LF_Logic_forallb__true__iff :
  ∀ (X : Type) (test : X → Original_LF__DOT__Basics_LF_Basics_bool) (l : Original_LF__DOT__Poly_LF_Poly_list X),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Logic_LF_Logic_forallb test l) Original_LF__DOT__Basics_LF_Basics_true)
        (Original_LF__DOT__Logic_LF_Logic_All (fun x => Corelib_Init_Logic_eq (test x) Original_LF__DOT__Basics_LF_Basics_true) l)

-- ============ And.and (LF.ProofObjects.Props.And) ============

inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and (P Q : Prop) : Prop where
  | conj : P → Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_And_and P Q

-- ============ TuplePlayground (bit, nybble, all_zero) ============

inductive Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit : Type where
  | B1 : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit
  | B0 : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit

inductive Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble : Type where
  | bits : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit →
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit →
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit →
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit →
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble

def Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero
    (nb : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble)
    : Original_LF__DOT__Basics_LF_Basics_bool :=
  match nb with
  | Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble.bits
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0 =>
        Original_LF__DOT__Basics_LF_Basics_bool.true
  | _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- ============ andb ============

def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool)
    : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- ============ andb3 ============

def Original_LF__DOT__Basics_LF_Basics_andb3 (b1 b2 b3 : Original_LF__DOT__Basics_LF_Basics_bool)
    : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_andb b1 (Original_LF__DOT__Basics_LF_Basics_andb b2 b3)

-- Test examples (proved via rfl)
theorem Original_LF__DOT__Basics_LF_Basics_test__andb32 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_andb3
      Original_LF__DOT__Basics_LF_Basics_false
      Original_LF__DOT__Basics_LF_Basics_true
      Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_false := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Basics_LF_Basics_test__andb34 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_andb3
      Original_LF__DOT__Basics_LF_Basics_true
      Original_LF__DOT__Basics_LF_Basics_true
      Original_LF__DOT__Basics_LF_Basics_false)
    Original_LF__DOT__Basics_LF_Basics_false := Corelib_Init_Logic_eq.refl _

-- ============ leb and ltb ============

def Original_LF__DOT__Basics_LF_Basics_leb (n m : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match n with
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S n' =>
    match m with
    | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
    | nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

def Original_LF__DOT__Basics_LF_Basics_ltb (n m : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_leb (nat.S n) m

-- Test examples for ltb (proved via rfl)
theorem Original_LF__DOT__Basics_LF_Basics_test__ltb2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_ltb (nat.S (nat.S nat.O)) (nat.S (nat.S (nat.S (nat.S nat.O)))))
    Original_LF__DOT__Basics_LF_Basics_true := Corelib_Init_Logic_eq.refl _

theorem Original_LF__DOT__Basics_LF_Basics_test__ltb3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_ltb (nat.S (nat.S (nat.S (nat.S nat.O)))) (nat.S (nat.S nat.O)))
    Original_LF__DOT__Basics_LF_Basics_false := Corelib_Init_Logic_eq.refl _

-- ============ apply_late_policy (Defined in Original.v) ============

noncomputable def Original_LF__DOT__Basics_LF_Basics_apply__late__policy
    (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade)
    : Original_LF__DOT__Basics_LF_Basics_grade :=
  match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))) with -- 9
  | Original_LF__DOT__Basics_LF_Basics_bool.true => g
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))) with -- 17
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_lower__grade g
    | Original_LF__DOT__Basics_LF_Basics_bool.false =>
      match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))) with -- 21
      | Original_LF__DOT__Basics_LF_Basics_bool.true =>
          Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g)
      | Original_LF__DOT__Basics_LF_Basics_bool.false =>
          Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g))

-- no_penalty_for_mostly_on_time (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_no__penalty__for__mostly__on__time :
  ∀ (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))
      Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_apply__late__policy late_days g) g

-- ============ orb' ============

def Original_LF__DOT__Basics_LF_Basics_orb' (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool)
    : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false => b2

-- ============ le2 (IndPrinciples) ============

inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 (n : nat) : nat → Prop where
  | le2_n : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n n
  | le2_S : ∀ m, Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n m →
                 Original_LF__DOT__IndPrinciples_LF_IndPrinciples_le2 n (nat.S m)

-- ============ discriminate_ex1 (Admitted in Original.v) ============

axiom Original_LF__DOT__Tactics_LF_Tactics_discriminate__ex1 :
  ∀ (n m : nat),
    Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq n m

-- ============ n_lt_m__n_le_m (Admitted in Original.v) ============

axiom Original_LF__DOT__IndProp_LF_IndProp_n__lt__m____n__le__m :
  ∀ (n m : nat), lt n m → le n m



