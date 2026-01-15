-- Comprehensive Lean 4 translation for all required Rocq definitions

set_option autoImplicit false

-- ==================== Basic Types ====================

-- True in Prop (will become SProp in Rocq)
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- ==================== Natural Numbers ====================

inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat.add
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Nat_add n' m)

-- Nat.mul
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Nat_add m (Nat_mul n' m)

-- le relation
inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- or type
inductive or (A B : Prop) : Prop where
  | or_introl : A → or A B
  | or_intror : B → or A B

-- and type
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- ==================== Boolean Types ====================

-- Original.LF_DOT_Basics.LF.Basics.bool
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
  | .true => .false
  | .false => .true

-- negb_involutive theorem (Admitted in original)
axiom Original_LF__DOT__Basics_LF_Basics_negb__involutive :
  ∀ (b : Original_LF__DOT__Basics_LF_Basics_bool),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_negb b)) b

-- ==================== bin type ====================

inductive Original_LF__DOT__Basics_LF_Basics_bin : Type where
  | Z : Original_LF__DOT__Basics_LF_Basics_bin
  | B0 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin
  | B1 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin

def Original_LF__DOT__Basics_LF_Basics_Z : Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.Z

def Original_LF__DOT__Basics_LF_Basics_B0 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B0

def Original_LF__DOT__Basics_LF_Basics_B1 : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin :=
  Original_LF__DOT__Basics_LF_Basics_bin.B1

-- incr is Admitted axiom in original
axiom Original_LF__DOT__Basics_LF_Basics_incr : Original_LF__DOT__Basics_LF_Basics_bin → Original_LF__DOT__Basics_LF_Basics_bin

-- test_bin_incr3 is Admitted in original
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B1 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
    (Original_LF__DOT__Basics_LF_Basics_B0 (Original_LF__DOT__Basics_LF_Basics_B0 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))

-- ==================== Grade Types ====================

-- Letter type: A, B, C, D, F
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

-- Modifier type: Plus, Natural, Minus
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- Grade type
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- ltb is Admitted axiom in original
axiom Original_LF__DOT__Basics_LF_Basics_ltb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool

-- lower_grade is Admitted axiom in original
axiom Original_LF__DOT__Basics_LF_Basics_lower__grade : Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade

-- apply_late_policy
noncomputable def Original_LF__DOT__Basics_LF_Basics_apply__late__policy (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade) : Original_LF__DOT__Basics_LF_Basics_grade :=
  match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))) with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => g
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))) with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_lower__grade g
    | Original_LF__DOT__Basics_LF_Basics_bool.false =>
      match Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))) with
      | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g)
      | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade (Original_LF__DOT__Basics_LF_Basics_lower__grade g))

-- grade_lowered_once is Admitted in original
axiom Original_LF__DOT__Basics_LF_Basics_grade__lowered__once :
  ∀ (late_days : nat) (g : Original_LF__DOT__Basics_LF_Basics_grade),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))) Original_LF__DOT__Basics_LF_Basics_false →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_ltb late_days (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_apply__late__policy late_days g) (Original_LF__DOT__Basics_LF_Basics_lower__grade g)

-- ==================== Lists ====================

-- natprod type (pair of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

def Original_LF__DOT__Lists_LF_Lists_NatList_pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair

def Original_LF__DOT__Lists_LF_Lists_NatList_fst (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x

def Original_LF__DOT__Lists_LF_Lists_NatList_snd (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair _ y => y

-- surjective_pairing theorem (Admitted in original)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_surjective__pairing : ∀ (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  Corelib_Init_Logic_eq
    p
    (Original_LF__DOT__Lists_LF_Lists_NatList_pair
       (Original_LF__DOT__Lists_LF_Lists_NatList_fst p)
       (Original_LF__DOT__Lists_LF_Lists_NatList_snd p))

-- ==================== Polymorphic List ====================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- filter_even_gt7 is Admitted in original
axiom Original_LF__DOT__Poly_LF_Poly_filter__even__gt7 :
  Original_LF__DOT__Poly_LF_Poly_list nat → Original_LF__DOT__Poly_LF_Poly_list nat

-- test_filter_even_gt7_1 is Admitted in original
axiom Original_LF__DOT__Poly_LF_Poly_test__filter__even__gt7__1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter__even__gt7
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))
                (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0)))))))))
                   (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))
                      (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S _0)))
                         (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))))
                            (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))
                               (Original_LF__DOT__Poly_LF_Poly_nil nat))))))))))
    (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))))
          (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))
             (Original_LF__DOT__Poly_LF_Poly_nil nat))))

-- ==================== Induction ====================

-- mul_0_r theorem (Admitted in original)
axiom Original_LF__DOT__Induction_LF_Induction_mul__0__r : ∀ (n : nat),
  Corelib_Init_Logic_eq (Nat_mul n nat.O) nat.O

-- mult_plus_distr_r theorem (Admitted in original)
axiom Original_LF__DOT__Induction_LF_Induction_mult__plus__distr__r : ∀ (n m p : nat),
  Corelib_Init_Logic_eq (Nat_mul (Nat_add n m) p) (Nat_add (Nat_mul n p) (Nat_mul m p))

-- ==================== Logic ====================

-- and_example' theorem (Admitted in original)
-- 3 + 4 = 7 /\ 2 * 2 = 4
axiom Original_LF__DOT__Logic_LF_Logic_and__example' :
  and
    (Corelib_Init_Logic_eq (Nat_add (S (S (S _0))) (S (S (S (S _0))))) (S (S (S (S (S (S (S _0))))))))
    (Corelib_Init_Logic_eq (Nat_mul (S (S _0)) (S (S _0))) (S (S (S (S _0)))))

-- and_example2'' theorem (Admitted in original)
axiom Original_LF__DOT__Logic_LF_Logic_and__example2'' : ∀ (n m : nat),
  Corelib_Init_Logic_eq n _0 → Corelib_Init_Logic_eq m _0 → Corelib_Init_Logic_eq (Nat_add n m) _0

-- ==================== IndProp ====================

-- plus_le_cases theorem (Admitted in original)
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__le__cases : ∀ (n m p q : nat),
  le (Nat_add n m) (Nat_add p q) →
  or (le n p) (le m q)

-- ==================== Rel ====================

-- le_S_n theorem (Admitted in original)
axiom Original_LF_Rel_le__S__n : ∀ (n m : nat),
  le (S n) (S m) → le n m

-- ==================== Auto ====================

-- Helper for 42
def nat42 : nat :=
  nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S
  (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S
  (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S
  (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S
  (nat.S (nat.S _0)))))))))))))))))))))))))))))))))))))))))

-- is_fortytwo definition: x = 42
def Original_LF__DOT__Auto_LF_Auto_is__fortytwo (x : nat) : Prop :=
  Corelib_Init_Logic_eq x nat42

-- auto_example_7' theorem (Admitted in original)
axiom Original_LF__DOT__Auto_LF_Auto_auto__example__7' : ∀ (x : nat),
  (and (le x nat42) (le nat42 x)) → Original_LF__DOT__Auto_LF_Auto_is__fortytwo x

-- ==================== AltAuto ====================

-- trans_example1' theorem (Admitted in original)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_trans__example1' : ∀ (a b c d : nat),
  le a (Nat_add b (Nat_mul b c)) →
  le (Nat_mul (Nat_add (S _0) c) b) d →
  le a d

-- ==================== Tactics ====================

-- square definition
def Original_LF__DOT__Tactics_LF_Tactics_square (n : nat) : nat :=
  Nat_mul n n

-- square_mult theorem (Admitted in original)
axiom Original_LF__DOT__Tactics_LF_Tactics_square__mult : ∀ (n m : nat),
  Corelib_Init_Logic_eq (Original_LF__DOT__Tactics_LF_Tactics_square (Nat_mul n m))
    (Nat_mul (Original_LF__DOT__Tactics_LF_Tactics_square n) (Original_LF__DOT__Tactics_LF_Tactics_square m))

-- ==================== ProofObjects ====================

-- curry theorem (Admitted in original)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_curry : ∀ (P Q R : Prop),
  (and P Q → R) → P → Q → R

-- ==================== Basics additional ====================

-- bin_to_nat is Admitted axiom in original
axiom Original_LF__DOT__Basics_LF_Basics_bin__to__nat : Original_LF__DOT__Basics_LF_Basics_bin → nat

-- plus_1_l theorem (Admitted in original)
axiom Original_LF__DOT__Basics_LF_Basics_plus__1__l : ∀ (n : nat),
  Corelib_Init_Logic_eq (Nat_add (S _0) n) (S n)

-- test_bin_incr2 is Admitted in original
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B0 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
    (Original_LF__DOT__Basics_LF_Basics_B1 (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z))

-- test_bin_incr5 is Admitted in original
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr5 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_bin__to__nat (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
    (Nat_add (S _0) (Original_LF__DOT__Basics_LF_Basics_bin__to__nat (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))

-- test_bin_incr6 is Admitted in original
axiom Original_LF__DOT__Basics_LF_Basics_test__bin__incr6 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_bin__to__nat (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_incr (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z))))
    (Nat_add (S (S _0)) (Original_LF__DOT__Basics_LF_Basics_bin__to__nat (Original_LF__DOT__Basics_LF_Basics_B1 Original_LF__DOT__Basics_LF_Basics_Z)))
