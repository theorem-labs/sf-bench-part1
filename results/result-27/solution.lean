-- Comprehensive Lean translation for all required isomorphisms
set_option autoImplicit false
set_option linter.unusedVariables false

-- ==================== Basic Types ====================

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat addition
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

-- Nat multiplication
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- ==================== Logic Types ====================

-- True in Prop (named RocqTrue to avoid conflict with Lean's True)
inductive RocqTrue : Prop where
  | intro : RocqTrue

def RocqTrue_intro : RocqTrue := RocqTrue.intro

-- False in Prop (empty type)
inductive RocqFalse : Prop where

-- Logic.not definition
def Logic_not (P : Prop) : Prop := P → RocqFalse

-- Equality in Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop arguments (needed for Corelib_Init_Logic_eq_Prop isomorphism)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- And (conjunction)
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Or (disjunction) - for Corelib or
inductive or (A B : Prop) : Prop where
  | inl (h : A) : or A B
  | inr (h : B) : or A B

def or_introl := @or.inl
def or_intror := @or.inr

-- Existential
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- le (less than or equal) as inductive
inductive le : nat → nat → Prop where
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m → le n (nat.S m)

-- ==================== Bool Types ====================

-- Bool for RocqBool (will be mapped to bool)
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

-- Bool for Original.LF_DOT_Basics.LF.Basics.bool
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- ==================== Polymorphic List ====================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

def Original_LF__DOT__Poly_LF_Poly_length (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X) : nat :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length X t)

-- ==================== NatList (from Lists) ====================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- nat equality (eqb)
def Nat_eqb : nat → nat → RocqBool
  | nat.O, nat.O => RocqBool.true
  | nat.S n, nat.S m => Nat_eqb n m
  | _, _ => RocqBool.false

-- count function (implementation since original is Admitted)
def Original_LF__DOT__Lists_LF_Lists_NatList_count : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → nat
  | _, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => nat.O
  | v, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
    match Nat_eqb v h with
    | RocqBool.true => nat.S (Original_LF__DOT__Lists_LF_Lists_NatList_count v t)
    | RocqBool.false => Original_LF__DOT__Lists_LF_Lists_NatList_count v t

-- remove_one function (implementation since original is Admitted)
def Original_LF__DOT__Lists_LF_Lists_NatList_remove__one : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag
  | _, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | v, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
    match Nat_eqb v h with
    | RocqBool.true => t
    | RocqBool.false => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one v t)

-- remove_all function (implementation since original is Admitted)
def Original_LF__DOT__Lists_LF_Lists_NatList_remove__all : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag
  | _, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | v, Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
    match Nat_eqb v h with
    | RocqBool.true => Original_LF__DOT__Lists_LF_Lists_NatList_remove__all v t
    | RocqBool.false => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all v t)

-- sum function (bag append - implementation since original is Admitted)
def Original_LF__DOT__Lists_LF_Lists_NatList_sum : Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Lists_LF_Lists_NatList_bag
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_sum t l2)

-- test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0 (now a theorem)
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                      Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
    _0 := Corelib_Init_Logic_eq.refl _

-- ==================== Regular Expressions (IndProp) ====================

inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char {T : Type} (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union {T : Type} (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star {T : Type} (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- exp_match inductive relation
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re) →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- EmptySet inductive type
inductive Original_LF__DOT__IndProp_LF_IndProp_EmptySet_ind : Original_LF__DOT__Poly_LF_Poly_list nat → Prop where

-- EmptySet_is_empty is an axiom (Admitted) - polymorphic over T
axiom Original_LF__DOT__IndProp_LF_IndProp_EmptySet__is__empty :
  ∀ (T : Type) (s : Original_LF__DOT__Poly_LF_Poly_list T), Logic_not (Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__IndProp_LF_IndProp_EmptySet T))

-- subseq inductive type (empty - no constructors)
inductive Original_LF__DOT__IndProp_LF_IndProp_subseq : Original_LF__DOT__Poly_LF_Poly_list nat → Original_LF__DOT__Poly_LF_Poly_list nat → Prop where

-- subseq_app is an axiom (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_subseq__app :
  (l1 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  (l2 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  (l3 : Original_LF__DOT__Poly_LF_Poly_list nat) →
  Original_LF__DOT__IndProp_LF_IndProp_subseq l1 l2 →
  Original_LF__DOT__IndProp_LF_IndProp_subseq l1 (Original_LF__DOT__Poly_LF_Poly_app nat l2 l3)

-- plus_le is an axiom (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__le :
  ∀ (n1 n2 m : nat), le (Nat_add n1 n2) m → and (le n1 m) (le n2 m)

-- ==================== IndPrinciples ====================

-- rgb type
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_rgb : Type where
  | red : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_rgb
  | green : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_rgb
  | blue : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_rgb

-- Toy type (empty inductive)
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy : Type where

-- Toy_correct is an axiom (Admitted)
-- Original: exists f g, forall P : Toy -> Prop, (forall b : bool, P (f b)) -> 
--           (forall (n : nat) (t : Toy), P t -> P (g n t)) -> forall t : Toy, P t
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy__correct :
  ex (fun f : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
    ex (fun g : nat → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy =>
      ∀ P : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy → Prop,
        (∀ b : Original_LF__DOT__Basics_LF_Basics_bool, P (f b)) →
        (∀ (n : nat) (t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy), P t → P (g n t)) →
        ∀ t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_Toy, P t))

-- ==================== ProofObjects ====================

-- or type
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P Q : Prop) : Prop where
  | or_introl : P → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q
  | or_intror : Q → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q

-- inj_l
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_inj__l (P Q : Prop) (HP : P) : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or P Q :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl HP

-- ex type (for ProofObjects existential)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro (x : A) (h : P x) : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- de_morgan_not_or
-- de_morgan_not_or: uses standard or (not Props.or)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_de__morgan__not__or (P Q : Prop) (H : Logic_not (or P Q))
  : and (Logic_not P) (Logic_not Q) :=
  and.intro
    (fun p => H (or.inl p))
    (fun q => H (or.inr q))

-- dist_exists_or_term
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_dist__exists__or__term {X : Type} (P Q : X → Prop)
  (H : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun x => Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (P x) (Q x)))
  : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P) (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex Q) :=
  match H with
  | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x Hx =>
    match Hx with
    | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl HPx =>
      Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_introl (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x HPx)
    | Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_intror HQx =>
      Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_or.or_intror (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro x HQx)

-- eq type (for ProofObjects)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ (x : X), Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x x

-- leibniz_equality__equality
def Original_LF__DOT__ProofObjects_LF_ProofObjects_leibniz__equality____equality {X : Type} (x y : X) 
    (H : ∀ (P : X → Prop), P x → P y) : Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x y :=
  H (fun z => Original_LF__DOT__ProofObjects_LF_ProofObjects_eq x z) (Original_LF__DOT__ProofObjects_LF_ProofObjects_eq.eq_refl x)

-- ==================== Tactics ====================

-- square
def Original_LF__DOT__Tactics_LF_Tactics_square (n : nat) : nat :=
  Nat_mul n n

-- square_mult is an axiom (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_square__mult :
  ∀ (n m : nat),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Tactics_LF_Tactics_square (Nat_mul n m))
      (Nat_mul (Original_LF__DOT__Tactics_LF_Tactics_square n) (Original_LF__DOT__Tactics_LF_Tactics_square m))

-- bool_fn_applied_thrice is an axiom (Admitted)
axiom Original_LF__DOT__Tactics_LF_Tactics_bool__fn__applied__thrice :
  ∀ (f : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool) (b : Original_LF__DOT__Basics_LF_Basics_bool),
    Corelib_Init_Logic_eq (f (f (f b))) (f b)

-- ==================== Induction ====================

-- add_shuffle3' is an axiom (Admitted)
axiom Original_LF__DOT__Induction_LF_Induction_add__shuffle3' :
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add m (Nat_add n p))

-- ==================== Logic ====================

-- add_comm3_take3 is an axiom (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_add__comm3__take3 :
  ∀ (n m p : nat), Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- not_implies_our_not
def Original_LF__DOT__Logic_LF_Logic_not__implies__our__not (P : Prop) (H : Logic_not P) : (∀ Q : Prop, P → Q) :=
  fun _ hp => nomatch H hp

-- ==================== Tactics (eq_implies_succ_equal) ====================

-- eq_implies_succ_equal: n = m -> S n = S m
def Original_LF__DOT__Tactics_LF_Tactics_eq__implies__succ__equal (n m : nat) (H : Corelib_Init_Logic_eq n m) : Corelib_Init_Logic_eq (S n) (S m) :=
  match H with
  | Corelib_Init_Logic_eq.refl _ => Corelib_Init_Logic_eq.refl _

-- ==================== AltAuto ====================

-- contras: P -> ~P -> 0 = 1
def Original_LF__DOT__AltAuto_LF_AltAuto_contras (P : Prop) (HP : P) (HnP : Logic_not P) : Corelib_Init_Logic_eq _0 (S _0) :=
  nomatch HnP HP

-- match_ex2': True /\ True
def Original_LF__DOT__AltAuto_LF_AltAuto_match__ex2' : and RocqTrue RocqTrue :=
  and.intro RocqTrue.intro RocqTrue.intro

-- ==================== Test theorems ====================

-- test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__one3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S _0))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__one 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                            Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (S (S _0)) := Corelib_Init_Logic_eq.refl _

-- test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                         Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))))
    _0 := Corelib_Init_Logic_eq.refl _

-- test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                      Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))
    _0 := Corelib_Init_Logic_eq.refl _

-- test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S _0))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                            Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))
    (S (S _0)) := Corelib_Init_Logic_eq.refl _

-- test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__remove__all4 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S (S (S (S (S _0)))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_remove__all 
          (S (S (S (S (S _0)))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                   (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                         (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                               (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
                                  (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                                     (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                                        Original_LF__DOT__Lists_LF_Lists_NatList_nil))))))))))))
    _0 := Corelib_Init_Logic_eq.refl _

-- test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__sum1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_count 
       (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_sum 
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
                   Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
                   Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))
    (S (S (S _0))) := Corelib_Init_Logic_eq.refl _

