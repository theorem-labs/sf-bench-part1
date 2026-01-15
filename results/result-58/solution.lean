-- Lean 4 translation for pumping lemma and all dependencies
set_option autoImplicit false

-- False proposition 
inductive MyFalse : Prop where

-- True proposition
inductive MyTrue : Prop where
  | intro : MyTrue

-- Original.False (separate from MyFalse)
inductive Original_False : Prop where

-- Equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Specialization of eq at Prop (needed by checker)
-- Interface expects: forall x : SProp, x -> x -> SProp
-- This means: given an SProp type A (a Prop), and two inhabitants a b of A, return an SProp
-- We need a separate inductive for Prop-indexed equality
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Conjunction
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Existential quantifier
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- Negation
def Logic_not (P : Prop) : Prop := P → MyFalse

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

-- le as Prop based on boolean
def le (n m : nat) : Prop := Corelib_Init_Logic_eq (nat_leb n m) RocqBool.true

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- List length function
def Original_LF__DOT__Poly_LF_Poly_length (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length X t)

-- Regular expression type
inductive Original_LF__DOT__IndProp_LF_IndProp_reg__exp (T : Type) : Type where
  | EmptySet : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | EmptyStr : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Char : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | App : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Union : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T
  | Star : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T

-- Constructor exports for reg_exp
def Original_LF__DOT__IndProp_LF_IndProp_EmptySet (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet

def Original_LF__DOT__IndProp_LF_IndProp_EmptyStr (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) (t : T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char t

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) (r1 r2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union r1 r2

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) (r : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r

-- exp_match inductive (propositional type)
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_list.cons x Original_LF__DOT__Poly_LF_Poly_list.nil) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
         (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
       : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
            (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2)
          : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) 
         : Original_LF__DOT__IndProp_LF_IndProp_exp__match Original_LF__DOT__Poly_LF_Poly_list.nil (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
             (H1 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re)
             (H2 : Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re))
           : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- pumping_constant function
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant {T : Type} (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) : nat :=
  match re with
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptySet => nat.S nat.O
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr => nat.S nat.O
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char _ => nat.S (nat.S nat.O)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2 =>
      Nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1)
              (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2 =>
      Nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1)
              (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star r =>
      Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant r

-- The napp function (repeat append n times)
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp (X : Type) : nat → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | nat.O, _ => Original_LF__DOT__Poly_LF_Poly_list.nil
  | nat.S n', l => Original_LF__DOT__Poly_LF_Poly_app X l (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp X n' l)

-- The main pumping lemma (Admitted in Original.v, so we use an axiom)
-- pumping : forall T (re : reg_exp T) s,
--   s =~ re ->
--   pumping_constant re <= length s ->
--   exists s1 s2 s3,
--     s = s1 ++ s2 ++ s3 /\
--     s2 <> [] /\
--     length s1 + length s2 <= pumping_constant re /\
--     (forall m : nat, s1 ++ napp m s2 ++ s3 =~ re)
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s re →
    le (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re) (Original_LF__DOT__Poly_LF_Poly_length T s) →
    ex (fun s1 : Original_LF__DOT__Poly_LF_Poly_list T =>
      ex (fun s2 : Original_LF__DOT__Poly_LF_Poly_list T =>
        ex (fun s3 : Original_LF__DOT__Poly_LF_Poly_list T =>
          and (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_app T s1 (Original_LF__DOT__Poly_LF_Poly_app T s2 s3)))
            (and (Logic_not (Corelib_Init_Logic_eq s2 (Original_LF__DOT__Poly_LF_Poly_nil T)))
              (and (le (Nat_add (Original_LF__DOT__Poly_LF_Poly_length T s1) (Original_LF__DOT__Poly_LF_Poly_length T s2))
                       (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re))
                (∀ (m : nat),
                  Original_LF__DOT__IndProp_LF_IndProp_exp__match 
                    (Original_LF__DOT__Poly_LF_Poly_app T s1 
                      (Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp T m s2) s3)) 
                    re))))))

-- ===== Additional definitions for other isomorphisms =====

-- Zero and successor definitions for nat
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Inductive le (Peano style)
inductive le2 : nat → nat → Prop where
  | le_n (n : nat) : le2 n n
  | le_S (n m : nat) : le2 n m → le2 n (nat.S m)

-- lt is defined in terms of le2
def lt (n m : nat) : Prop := le2 (nat.S n) m

-- Iff definition
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- nor definition for AltAuto
inductive Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop where
  | stroke : Logic_not P → Logic_not Q → Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q

-- Boolean type for Basics
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb for nat
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- ===== Axioms for Admitted theorems =====

-- imp3 axiom (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_imp3 :
  ∀ (P Q R : Prop), (P → Q → R) → Q → P → R

-- nor_not_and' axiom (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__and' :
  ∀ (P Q : Prop), Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q → and P Q → MyFalse

-- plus_1_neq_0' axiom (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_plus__1__neq__0' :
  ∀ (x : nat), Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add x (S _0)) _0)
    Original_LF__DOT__Basics_LF_Basics_false

-- plus_lt axiom (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_plus__lt :
  ∀ (n1 n2 m : nat), lt (Nat_add n1 n2) m → and (lt n1 m) (lt n2 m)

-- proof_irrelevance definition (not an axiom - it's a type)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), Corelib_Init_Logic_eq_Prop pf1 pf2

-- propositional_extensionality definition (not an axiom - it's a type)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality : Prop :=
  ∀ (P Q : Prop), iff P Q → Corelib_Init_Logic_eq P Q

-- pe_implies_pi axiom (Admitted in Original.v)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__pi :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality →
  Original_LF__DOT__ProofObjects_LF_ProofObjects_proof__irrelevance

-- weak_pumping axiom (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_weak__pumping :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s re →
    le (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re) (Original_LF__DOT__Poly_LF_Poly_length T s) →
    ex (fun s1 : Original_LF__DOT__Poly_LF_Poly_list T =>
      ex (fun s2 : Original_LF__DOT__Poly_LF_Poly_list T =>
        ex (fun s3 : Original_LF__DOT__Poly_LF_Poly_list T =>
          and (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_app T s1 (Original_LF__DOT__Poly_LF_Poly_app T s2 s3)))
            (and (Logic_not (Corelib_Init_Logic_eq s2 (Original_LF__DOT__Poly_LF_Poly_nil T)))
              (∀ (m : nat),
                Original_LF__DOT__IndProp_LF_IndProp_exp__match 
                  (Original_LF__DOT__Poly_LF_Poly_app T s1 
                    (Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp T m s2) s3)) 
                  re)))))

-- ===== Additional definitions for orb, In, filter, All, forallb =====

-- orb function
def Original_LF__DOT__Basics_LF_Basics_orb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false, b => b

-- test_orb1: (orb true false) = true
def Original_LF__DOT__Basics_LF_Basics_test__orb1 : Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_orb Original_LF__DOT__Basics_LF_Basics_true Original_LF__DOT__Basics_LF_Basics_false)
    Original_LF__DOT__Basics_LF_Basics_true :=
  Corelib_Init_Logic_eq.refl

-- test_orb4: (orb true true) = true
def Original_LF__DOT__Basics_LF_Basics_test__orb4 : Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_orb Original_LF__DOT__Basics_LF_Basics_true Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_true :=
  Corelib_Init_Logic_eq.refl

-- test_orb5: false || false || true = true (i.e., orb (orb false false) true = true)
def Original_LF__DOT__Basics_LF_Basics_test__orb5 : Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_orb 
      (Original_LF__DOT__Basics_LF_Basics_orb Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_false) 
      Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_true :=
  Corelib_Init_Logic_eq.refl

-- Disjunction in Prop
inductive Logic_or (A B : Prop) : Prop where
  | inl : A → Logic_or A B
  | inr : B → Logic_or A B

-- In predicate (membership)
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Corelib_Init_Logic_eq h x ∨ Original_LF__DOT__Logic_LF_Logic_In x t

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) 
    : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- All predicate (for forallb_true_iff) - Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_All : {T : Type} → (T → Prop) → Original_LF__DOT__Poly_LF_Poly_list T → Prop

-- forallb function - Admitted in Original.v (only signature given)
axiom Original_LF__DOT__Logic_LF_Logic_forallb : {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- forallb_true_iff - Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_forallb__true__iff :
  ∀ (X : Type) (test : X → Original_LF__DOT__Basics_LF_Basics_bool) (l : Original_LF__DOT__Poly_LF_Poly_list X),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Logic_LF_Logic_forallb test l) Original_LF__DOT__Basics_LF_Basics_true)
        (Original_LF__DOT__Logic_LF_Logic_All (fun x => Corelib_Init_Logic_eq (test x) Original_LF__DOT__Basics_LF_Basics_true) l)

-- not_true_is_false' - Admitted in Original.v
axiom Original_LF__DOT__Logic_LF_Logic_not__true__is__false' :
  ∀ (b : Original_LF__DOT__Basics_LF_Basics_bool),
    Logic_not (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_true) →
    Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_false

-- not_equiv_false - Admitted in Original.v
axiom Original_LF__DOT__IndProp_LF_IndProp_not__equiv__false :
  ∀ (P : Prop), Logic_not P → iff P Original_False

-- filter_not_empty_In' - Admitted in Original.v
axiom «Original_LF__DOT__IndProp_LF_IndProp_filter__not__empty__In'» :
  ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    Logic_not (Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_filter (fun x => Original_LF__DOT__Basics_LF_Basics_eqb n x) l) 
      (Original_LF__DOT__Poly_LF_Poly_nil nat)) →
    Original_LF__DOT__Logic_LF_Logic_In n l

-- pe_implies_true_eq - Admitted in Original.v
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__true__eq :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality →
  ∀ (P : Prop), P → Corelib_Init_Logic_eq MyTrue P
