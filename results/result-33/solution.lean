-- Comprehensive Lean translation merging multiple solutions
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat_add to match Rocq's Nat.add
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Boolean for le definition  
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

-- Less than or equal (boolean version)
def nat_leb : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_leb n m

-- Equality in Prop (which imports as SProp in Rocq)
universe u
inductive Corelib_Init_Logic_eq {A : Sort u} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- le as Prop based on boolean
def le (n m : nat) : Prop := Corelib_Init_Logic_eq (nat_leb n m) RocqBool.true

-- Conjunction
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Disjunction
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

-- Equality for Prop arguments (also imports as SProp → SProp → SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True proposition
inductive MyTrue : Prop where
  | intro : MyTrue

-- Define bool (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Define leb (less or equal for booleans)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.A

def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.B

def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.C

def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.D

def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter :=
  Original_LF__DOT__Basics_LF_Basics_letter.F

-- modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Plus

def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Natural

def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier :=
  Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- grade type: Grade letter modifier
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

-- comparison type: Eq, Lt, Gt
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Eq

def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Lt

def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- grade_comparison is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_grade__comparison :
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_comparison

-- test_grade_comparison4 is an axiom (Admitted in Coq)
axiom Original_LF__DOT__Basics_LF_Basics_test__grade__comparison4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_grade__comparison
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_B Original_LF__DOT__Basics_LF_Basics_Minus)
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_C Original_LF__DOT__Basics_LF_Basics_Plus))
    Original_LF__DOT__Basics_LF_Basics_Gt

-- Define natlist (list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nil alias
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

-- cons constructor as a definition
def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- bag is just an alias for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- app function
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 =>
      Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- test_app3: [] ++ [1;2;3] = [1;2;3] (Admitted, so axiom)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__app3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app
       Original_LF__DOT__Lists_LF_Lists_NatList_nil
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))

-- count is admitted in the original Rocq code, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat

-- remove_one is admitted in the original Rocq code, so axiom here
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__one : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag

-- The theorem remove_does_not_increase_count (admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_remove__does__not__increase__count :
  ∀ (x : Original_LF__DOT__Lists_LF_Lists_NatList_bag),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_leb
        (Original_LF__DOT__Lists_LF_Lists_NatList_count _0 (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one _0 x))
        (Original_LF__DOT__Lists_LF_Lists_NatList_count _0 x))
      Original_LF__DOT__Basics_LF_Basics_true

-- cnat type: forall X : Type, (X -> X) -> X -> X
abbrev Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 :=
  (X : Type) → (X → X) → X → X

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- two: forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_two : (X : Type) → (X → X) → X → X :=
  fun (X : Type) (f : X → X) (x : X) => f (f x)

-- three: forall X : Type, (X -> X) -> X -> X
def Original_LF__DOT__Poly_LF_Poly_Exercises_three : (X : Type) → (X → X) → X → X :=
  Original_LF__DOT__Poly_LF_Poly_doit3times

-- plus is admitted in Rocq, so we declare it as an axiom
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus :
  ((X : Type) → (X → X) → X → X) →
  ((X : Type) → (X → X) → X → X) →
  (X : Type) → (X → X) → X → X

-- plus_2 : plus two three = plus three two (an admitted theorem)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_plus__2 :
  @Corelib_Init_Logic_eq ((X : Type) → (X → X) → X → X)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus
       Original_LF__DOT__Poly_LF_Poly_Exercises_two
       Original_LF__DOT__Poly_LF_Poly_Exercises_three)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_plus
       Original_LF__DOT__Poly_LF_Poly_Exercises_three
       Original_LF__DOT__Poly_LF_Poly_Exercises_two)

-- add_assoc'' is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc'' :
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- auto_example_6' is Admitted in Original.v
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6' :
  ∀ (n m p : nat),
    (le n p → and (le n m) (le m n)) →
    le n p →
    Corelib_Init_Logic_eq n m

-- True_is_true : True (admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_True__is__true : MyTrue

-- consequentia_mirabilis: forall P:Prop, (~P -> P) -> P
def Original_LF__DOT__Logic_LF_Logic_consequentia__mirabilis : Prop :=
  ∀ (P : Prop), (¬P → P) → P

-- proj1: forall P Q : Prop, P /\ Q -> P
def Original_LF__DOT__Logic_LF_Logic_proj1 (P Q : Prop) (H : and P Q) : P :=
  H.left

-- lower_grade function
-- lower_grade lowers a grade by one step:
-- Plus -> Natural -> Minus -> (next letter) Plus
def next_letter : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_letter
  | Original_LF__DOT__Basics_LF_Basics_letter.A => Original_LF__DOT__Basics_LF_Basics_letter.B
  | Original_LF__DOT__Basics_LF_Basics_letter.B => Original_LF__DOT__Basics_LF_Basics_letter.C
  | Original_LF__DOT__Basics_LF_Basics_letter.C => Original_LF__DOT__Basics_LF_Basics_letter.D
  | Original_LF__DOT__Basics_LF_Basics_letter.D => Original_LF__DOT__Basics_LF_Basics_letter.F
  | Original_LF__DOT__Basics_LF_Basics_letter.F => Original_LF__DOT__Basics_LF_Basics_letter.F

def Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade
  | Original_LF__DOT__Basics_LF_Basics_grade.Grade l Original_LF__DOT__Basics_LF_Basics_modifier.Plus =>
      Original_LF__DOT__Basics_LF_Basics_grade.Grade l Original_LF__DOT__Basics_LF_Basics_modifier.Natural
  | Original_LF__DOT__Basics_LF_Basics_grade.Grade l Original_LF__DOT__Basics_LF_Basics_modifier.Natural =>
      Original_LF__DOT__Basics_LF_Basics_grade.Grade l Original_LF__DOT__Basics_LF_Basics_modifier.Minus
  | Original_LF__DOT__Basics_LF_Basics_grade.Grade l Original_LF__DOT__Basics_LF_Basics_modifier.Minus =>
      Original_LF__DOT__Basics_LF_Basics_grade.Grade (next_letter l) Original_LF__DOT__Basics_LF_Basics_modifier.Plus

-- Props.True (in ProofObjects)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True : Prop where
  | I : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True

-- p_implies_true: forall P, P -> True
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_p__implies__true
    (P : Type) (_ : P) : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_True.I

-- add_assoc_from_induction: forall n m p : nat, n + (m + p) = (n + m) + p (Admitted in Original)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_add__assoc__from__induction :
  ∀ (n m p : nat),
    @Corelib_Init_Logic_eq nat (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- auto_example_6: Admitted in Original.v
-- forall n m p : nat, (n <= p -> n <= m /\ m <= n) -> n <= p -> n = m
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__6 :
  ∀ (n m p : nat),
    (le n p → and (le n m) (le m n)) →
    le n p →
    @Corelib_Init_Logic_eq nat n m

-- le_antisym: Admitted in Original.v
-- forall n m : nat, n <= m /\ m <= n -> n = m
axiom Original_LF__DOT__AltAuto_LF_AltAuto_le__antisym :
  ∀ (n m : nat),
    and (le n m) (le m n) →
    @Corelib_Init_Logic_eq nat n m

-- Auto.auto_example_6: Admitted in Original.v
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__6 :
  ∀ (n m p : nat),
    (le n p → and (le n m) (le m n)) →
    le n p →
    @Corelib_Init_Logic_eq nat n m

-- Auto.le_antisym: Admitted in Original.v
-- forall n m : nat, n <= m /\ m <= n -> n = m
axiom Original_LF__DOT__Auto_LF_Auto_le__antisym :
  ∀ (n m : nat),
    and (le n m) (le m n) →
    @Corelib_Init_Logic_eq nat n m

-- IndProp.plus_le: Admitted in Original.v
-- forall n1 n2 m : nat, n1 + n2 <= m -> n1 <= m /\ n2 <= m
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__le :
  ∀ (n1 n2 m : nat),
    le (Nat_add n1 n2) m →
    and (le n1 m) (le n2 m)

-- IndProp.plus_le_cases: Admitted in Original.v  
-- forall n m p q : nat, n + m <= p + q -> n <= p \/ m <= q
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases :
  ∀ (n m p q : nat),
    le (Nat_add n m) (Nat_add p q) →
    or (le n p) (le m q)

-- IndProp.le_plus_l: Admitted in Original.v
-- forall a b : nat, a <= a + b
axiom Original_LF__DOT__IndProp_LF_IndProp_le__plus__l :
  ∀ (a b : nat), le a (Nat_add a b)

-- lower_grade_A_Natural: lower_grade (Grade A Natural) = Grade A Minus
theorem Original_LF__DOT__Basics_LF_Basics_lower__grade__A__Natural :
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_grade
    (Original_LF__DOT__Basics_LF_Basics_lower__grade
      (Original_LF__DOT__Basics_LF_Basics_grade.Grade
        Original_LF__DOT__Basics_LF_Basics_letter.A
        Original_LF__DOT__Basics_LF_Basics_modifier.Natural))
    (Original_LF__DOT__Basics_LF_Basics_grade.Grade
      Original_LF__DOT__Basics_LF_Basics_letter.A
      Original_LF__DOT__Basics_LF_Basics_modifier.Minus) :=
  Corelib_Init_Logic_eq.refl _

-- lower_grade_A_Plus: lower_grade (Grade A Plus) = Grade A Natural
theorem Original_LF__DOT__Basics_LF_Basics_lower__grade__A__Plus :
  @Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_grade
    (Original_LF__DOT__Basics_LF_Basics_lower__grade
      (Original_LF__DOT__Basics_LF_Basics_grade.Grade
        Original_LF__DOT__Basics_LF_Basics_letter.A
        Original_LF__DOT__Basics_LF_Basics_modifier.Plus))
    (Original_LF__DOT__Basics_LF_Basics_grade.Grade
      Original_LF__DOT__Basics_LF_Basics_letter.A
      Original_LF__DOT__Basics_LF_Basics_modifier.Natural) :=
  Corelib_Init_Logic_eq.refl _


