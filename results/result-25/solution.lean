-- Comprehensive Lean 4 translation for all required isomorphisms
set_option autoImplicit false
set_option linter.unusedVariables false

-- ============================================================
-- Basic Types: True, False, Equality
-- ============================================================

-- False proposition 
inductive MyFalse : Prop where

-- Alias for Original.False
def Original_False : Prop := MyFalse

-- True proposition
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Specialization of eq at Prop (needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Equality for Prop (used in some proofs)
inductive Prop_eq {A : Prop} (a : A) : A → Prop where
  | refl : Prop_eq a a

-- ============================================================
-- Natural numbers
-- ============================================================

inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Nat_add m (Nat_mul n' m)

-- ============================================================
-- Logic: and, or, ex, not, iff
-- ============================================================

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

-- Disjunction
inductive or (A B : Prop) : Prop where
  | inl : A → or A B
  | inr : B → or A B

-- Iff (if and only if)
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- ============================================================
-- Boolean type (LF.Basics.bool)
-- ============================================================

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

-- andb function
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .true => b2
  | .false => .false

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => .true
  | nat.S nat.O => .false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- plus function
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- mult function
def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

-- eqb function (nat equality)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => .true
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_eqb n m
  | _, _ => .false

-- leb function (nat less-or-equal)
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, _ => .true
  | nat.S _, nat.O => .false
  | nat.S n, nat.S m => Original_LF__DOT__Basics_LF_Basics_leb n m

-- ltb function (nat strictly less than)
def Original_LF__DOT__Basics_LF_Basics_ltb (n m : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_leb (nat.S n) m

-- test_ltb1: ltb 2 2 = false (Admitted in Original)
axiom Original_LF__DOT__Basics_LF_Basics_test__ltb1 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_ltb (nat.S (nat.S nat.O)) (nat.S (nat.S nat.O))) Original_LF__DOT__Basics_LF_Basics_false

-- ============================================================
-- Boolean for le/lt definitions (RocqBool to avoid name collision)
-- ============================================================

inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def RocqBool_false : RocqBool := RocqBool.false
def RocqBool_true : RocqBool := RocqBool.true

-- Less than or equal (boolean version for le)
def nat_leb : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_leb n m

-- le as Prop based on boolean
def le (n m : nat) : Prop := Corelib_Init_Logic_eq (nat_leb n m) RocqBool.true

-- Successor for le
def le2 (n m : nat) : Prop := le (nat.S n) (nat.S m)

-- lt as Prop
def lt (n m : nat) : Prop := le (nat.S n) m

-- ============================================================
-- Polymorphic list type (LF.Poly.list)
-- ============================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | .nil, l2 => l2
  | .cons h t, l2 => .cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- List length
def Original_LF__DOT__Poly_LF_Poly_length (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | .nil => nat.O
  | .cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length X t)

-- ============================================================
-- NatList (LF.Lists.NatList)
-- ============================================================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- hd function
def Original_LF__DOT__Lists_LF_Lists_NatList_hd (default : nat) (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : nat :=
  match l with
  | .nil => default
  | .cons h _ => h

-- app function for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | .nil, l2 => l2
  | .cons h t, l2 => .cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- bag type (alias for natlist)
def Original_LF__DOT__Lists_LF_Lists_NatList_bag : Type := Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- member function (check if nat is in bag)
def Original_LF__DOT__Lists_LF_Lists_NatList_member : nat → Original_LF__DOT__Lists_LF_Lists_NatList_bag → Original_LF__DOT__Basics_LF_Basics_bool
  | _, .nil => .false
  | v, .cons h t => match Original_LF__DOT__Basics_LF_Basics_eqb v h with
    | .true => .true
    | .false => Original_LF__DOT__Lists_LF_Lists_NatList_member v t

-- mylist definition: [1;2;3]
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  .cons (nat.S nat.O) (.cons (nat.S (nat.S nat.O)) (.cons (nat.S (nat.S (nat.S nat.O))) .nil))

-- mylist3: another name for mylist
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_mylist

-- nil_app lemma (Admitted in Original): forall l, [] ++ l = l
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nil__app :
  ∀ (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
  Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_NatList_app .nil l) l

-- test_app3 (Admitted): [1;2;3] ++ nil = [1;2;3]
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__app3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app Original_LF__DOT__Lists_LF_Lists_NatList_mylist .nil)
    Original_LF__DOT__Lists_LF_Lists_NatList_mylist

-- test_member1 (Admitted): member 1 [1;4;1] = true
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__member1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_member (nat.S nat.O)
      (.cons (nat.S nat.O) (.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) (.cons (nat.S nat.O) .nil))))
    Original_LF__DOT__Basics_LF_Basics_true

-- ============================================================
-- Regular expressions and exp_match (LF.IndProp)
-- ============================================================

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

def Original_LF__DOT__IndProp_LF_IndProp_Char (T : Type) : T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char

def Original_LF__DOT__IndProp_LF_IndProp_App (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App

def Original_LF__DOT__IndProp_LF_IndProp_Union (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union

def Original_LF__DOT__IndProp_LF_IndProp_Star (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T :=
  Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star

-- exp_match inductive
inductive Original_LF__DOT__IndProp_LF_IndProp_exp__match {T : Type} : Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Prop where
  | MEmpty : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_nil T) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.EmptyStr)
  | MChar (x : T) : Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_cons T x (Original_LF__DOT__Poly_LF_Poly_nil T)) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Char x)
  | MApp (s1 : Original_LF__DOT__Poly_LF_Poly_list T) (re1 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
         (s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re1 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 re2 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.App re1 re2)
  | MUnionL (s : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s re1 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MUnionR (s : Original_LF__DOT__Poly_LF_Poly_list T) (re1 re2 : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s re2 →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Union re1 re2)
  | MStar0 (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_nil T) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)
  | MStarApp (s1 s2 : Original_LF__DOT__Poly_LF_Poly_list T) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) :
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s1 re →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match s2 (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re) →
    Original_LF__DOT__IndProp_LF_IndProp_exp__match (Original_LF__DOT__Poly_LF_Poly_app T s1 s2) (Original_LF__DOT__IndProp_LF_IndProp_reg__exp.Star re)

-- ============================================================
-- Pumping lemma definitions
-- ============================================================

-- pumping_constant
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant {T : Type} : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → nat
  | .EmptySet => nat.S nat.O
  | .EmptyStr => nat.S nat.O
  | .Char _ => nat.S (nat.S nat.O)
  | .App re1 re2 => Nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1) (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | .Union re1 re2 => Nat_add (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1) (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re2)
  | .Star re1 => Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re1

-- napp (repeat list n times)
def Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp (T : Type) : nat → Original_LF__DOT__Poly_LF_Poly_list T → Original_LF__DOT__Poly_LF_Poly_list T
  | nat.O, _ => Original_LF__DOT__Poly_LF_Poly_nil T
  | nat.S n', l => Original_LF__DOT__Poly_LF_Poly_app T l (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp T n' l)

-- ============================================================
-- Perm3 (permutation of 3-element lists)
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_Perm3 {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Prop where
  | perm3_swap12 (a b c : X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3
        (Original_LF__DOT__Poly_LF_Poly_cons X a (Original_LF__DOT__Poly_LF_Poly_cons X b (Original_LF__DOT__Poly_LF_Poly_cons X c (Original_LF__DOT__Poly_LF_Poly_nil X))))
        (Original_LF__DOT__Poly_LF_Poly_cons X b (Original_LF__DOT__Poly_LF_Poly_cons X a (Original_LF__DOT__Poly_LF_Poly_cons X c (Original_LF__DOT__Poly_LF_Poly_nil X))))
  | perm3_swap23 (a b c : X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3
        (Original_LF__DOT__Poly_LF_Poly_cons X a (Original_LF__DOT__Poly_LF_Poly_cons X b (Original_LF__DOT__Poly_LF_Poly_cons X c (Original_LF__DOT__Poly_LF_Poly_nil X))))
        (Original_LF__DOT__Poly_LF_Poly_cons X a (Original_LF__DOT__Poly_LF_Poly_cons X c (Original_LF__DOT__Poly_LF_Poly_cons X b (Original_LF__DOT__Poly_LF_Poly_nil X))))
  | perm3_trans (l1 l2 l3 : Original_LF__DOT__Poly_LF_Poly_list X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l1 l2 →
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l2 l3 →
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l1 l3

-- ============================================================
-- Logic.In predicate
-- ============================================================

def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | .nil => MyFalse
  | .cons x' l' => or (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__Logic_LF_Logic_In x l')

-- ============================================================
-- combine_odd_even
-- ============================================================

-- combine_odd_even: (nat -> Prop) -> (nat -> Prop) -> nat -> Prop
def Original_LF__DOT__Logic_LF_Logic_combine__odd__even (Podd Peven : nat → Prop) (n : nat) : Prop :=
  match Original_LF__DOT__Basics_LF_Basics_odd n with
  | .true => Podd n
  | .false => Peven n

-- ============================================================
-- Church numerals (cnat)
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 :=
  (X : Type) → (X → X) → X → X

def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ f x => f x

def Original_LF__DOT__Poly_LF_Poly_Exercises_two : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun _ f x => f (f x)

-- two' is defined as succ one
def Original_LF__DOT__Poly_LF_Poly_Exercises_succ (n : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat) : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun X f x => f (n X f x)

def Original_LF__DOT__Poly_LF_Poly_Exercises_twoPrime : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  Original_LF__DOT__Poly_LF_Poly_Exercises_succ Original_LF__DOT__Poly_LF_Poly_Exercises_one

-- ============================================================
-- fold function
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_fold (X Y : Type) (f : X → Y → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X) (b : Y) : Y :=
  match l with
  | .nil => b
  | .cons h t => f h (Original_LF__DOT__Poly_LF_Poly_fold X Y f t b)

-- ============================================================
-- AltAuto definitions (Admitted axioms)
-- ============================================================

-- nor function
def Original_LF__DOT__AltAuto_LF_AltAuto_nor (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (match b1 with
    | .true => .true
    | .false => b2)

-- andb_true_elim2 (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_andb__true__elim2 :
  ∀ (b c : Original_LF__DOT__Basics_LF_Basics_bool),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_andb b c) Original_LF__DOT__Basics_LF_Basics_true →
    Corelib_Init_Logic_eq c Original_LF__DOT__Basics_LF_Basics_true

-- simple_semi'' (Admitted in Original.v): forall n, (n + 1 =? 0) = false
axiom Original_LF__DOT__AltAuto_LF_AltAuto_simple__semiPrimePrime :
  ∀ (n : nat), Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add n (S _0)) _0)
    Original_LF__DOT__Basics_LF_Basics_false

-- ============================================================
-- Tactics definitions (Admitted axioms)
-- ============================================================

-- silly4 (Admitted in Original.v): forall n m p q, (n=m -> p=q) -> m=n -> q=p
axiom Original_LF__DOT__Tactics_LF_Tactics_silly4 :
  ∀ (n m p q : nat),
    (Corelib_Init_Logic_eq n m → Corelib_Init_Logic_eq p q) →
    Corelib_Init_Logic_eq m n →
    Corelib_Init_Logic_eq q p

-- ============================================================
-- IndProp axioms (Admitted in Original.v)
-- ============================================================

-- Perm3_rev (Admitted): specific lemma Perm3 [1;2;3] [3;2;1]
axiom Original_LF__DOT__IndProp_LF_IndProp_Perm3__rev :
  @Original_LF__DOT__IndProp_LF_IndProp_Perm3 nat
    (Original_LF__DOT__Poly_LF_Poly_cons nat (S _0)
      (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S _0))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S _0)))
          (Original_LF__DOT__Poly_LF_Poly_nil nat))))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S _0)))
      (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S _0))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (S _0)
          (Original_LF__DOT__Poly_LF_Poly_nil nat))))

-- pumping (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T),
    @Original_LF__DOT__IndProp_LF_IndProp_exp__match T s re →
    le (Original_LF__DOT__IndProp_LF_IndProp_Pumping_pumping__constant re) (Original_LF__DOT__Poly_LF_Poly_length T s) →
    ex (fun s1 : Original_LF__DOT__Poly_LF_Poly_list T =>
      ex (fun s2 : Original_LF__DOT__Poly_LF_Poly_list T =>
        ex (fun s3 : Original_LF__DOT__Poly_LF_Poly_list T =>
          and (Corelib_Init_Logic_eq s (Original_LF__DOT__Poly_LF_Poly_app T s1 (Original_LF__DOT__Poly_LF_Poly_app T s2 s3)))
            (and (Logic_not (Corelib_Init_Logic_eq s2 (Original_LF__DOT__Poly_LF_Poly_nil T)))
              (∀ (m : nat),
                @Original_LF__DOT__IndProp_LF_IndProp_exp__match T
                  (Original_LF__DOT__Poly_LF_Poly_app T s1 
                    (Original_LF__DOT__Poly_LF_Poly_app T (Original_LF__DOT__IndProp_LF_IndProp_Pumping_napp T m s2) s3)) 
                  re)))))

-- re_chars as separate definition
def Original_LF__DOT__IndProp_LF_IndProp_re__chars (T : Type) : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T → Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__IndProp_LF_IndProp_reg__exp T)
  | .EmptySet => .nil
  | .EmptyStr => .nil
  | .Char x => .cons (.Char x) .nil
  | .App re1 re2 => Original_LF__DOT__Poly_LF_Poly_app _ (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re1) (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re2)
  | .Union re1 re2 => Original_LF__DOT__Poly_LF_Poly_app _ (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re1) (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re2)
  | .Star re1 => Original_LF__DOT__IndProp_LF_IndProp_re__chars T re1

-- in_re_match (Admitted)
axiom Original_LF__DOT__IndProp_LF_IndProp_in__re__match :
  ∀ (T : Type) (re : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) (s : Original_LF__DOT__Poly_LF_Poly_list T) (x : T),
    @Original_LF__DOT__IndProp_LF_IndProp_exp__match T s re →
    @Original_LF__DOT__Logic_LF_Logic_In T x s →
    ex (fun re' : Original_LF__DOT__IndProp_LF_IndProp_reg__exp T =>
      and (@Original_LF__DOT__Logic_LF_Logic_In (Original_LF__DOT__IndProp_LF_IndProp_reg__exp T) re' (Original_LF__DOT__IndProp_LF_IndProp_re__chars T re))
           (@Original_LF__DOT__IndProp_LF_IndProp_exp__match T (Original_LF__DOT__Poly_LF_Poly_cons T x (Original_LF__DOT__Poly_LF_Poly_nil T)) re'))

-- ============================================================
-- Lists axioms (Admitted in Original.v)
-- ============================================================

-- leb_n_Sn (Admitted): forall n, n <=? S n = true
axiom Original_LF__DOT__Lists_LF_Lists_NatList_leb__n__Sn :
  ∀ (n : nat), Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_leb n (S n))
    Original_LF__DOT__Basics_LF_Basics_true

-- (mylist3 already defined earlier)

-- test_hd2 (Admitted): hd 0 [] = 0
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__hd2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd _0 Original_LF__DOT__Lists_LF_Lists_NatList_nil)
    _0

-- ============================================================
-- Logic axioms (Admitted in Original.v)
-- ============================================================

-- combine_odd_even_intro (Admitted)
axiom Original_LF__DOT__Logic_LF_Logic_combine__odd__even__intro :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    (Original_LF__DOT__Basics_LF_Basics_odd n = Original_LF__DOT__Basics_LF_Basics_true → Podd n) →
    (Original_LF__DOT__Basics_LF_Basics_odd n = Original_LF__DOT__Basics_LF_Basics_false → Peven n) →
    Original_LF__DOT__Logic_LF_Logic_combine__odd__even Podd Peven n

-- ============================================================
-- Poly axioms (Admitted in Original.v)
-- ============================================================

-- two' (Admitted): two' = two
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_twoPrime__eq :
  ∀ (X : Type), Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_Exercises_twoPrime X)
    (Original_LF__DOT__Poly_LF_Poly_Exercises_two X)

-- fold_example2 (Admitted): fold andb [true; true; false] true = false
axiom Original_LF__DOT__Poly_LF_Poly_fold__example2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_fold
      Original_LF__DOT__Basics_LF_Basics_bool
      Original_LF__DOT__Basics_LF_Basics_bool
      Original_LF__DOT__Basics_LF_Basics_andb
      (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
        (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_false
            (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool))))
      Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_false

-- list123' (Admitted): defines the list [1;2;3]
def Original_LF__DOT__Poly_LF_Poly_list123Prime : Original_LF__DOT__Poly_LF_Poly_list nat :=
  Original_LF__DOT__Poly_LF_Poly_cons nat (S _0)
    (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S _0))
      (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S _0)))
        (Original_LF__DOT__Poly_LF_Poly_nil nat)))

-- ============================================================
-- ProofObjects: ev predicate (evenness)
-- ============================================================

-- ev predicate: n is even
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O
  | ev_SS : ∀ (n : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n))

def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_0

def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev_SS (n : nat) (h : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n) : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n)) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n h

-- ev_4' (Admitted): ev 4
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4' : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S (nat.S (nat.S nat.O))))

-- ev_plus4': forall n, ev n -> ev (4 + n) (Not admitted - has definition!)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4' :
  ∀ (n : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n →
    Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S (nat.S (nat.S n)))) :=
  fun n H =>
    Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS (nat.S (nat.S n))
      (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n H)

-- ============================================================
-- Auto: silly2_eauto (Admitted)
-- ============================================================

-- silly2_eauto: forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
--   (exists y, P 42 y) -> (forall x y : nat, P x y -> Q x) -> Q 42.
axiom Original_LF__DOT__Auto_LF_Auto_silly2__eauto :
  ∀ (P : nat → nat → Prop) (Q : nat → Prop),
    ex (fun y => P (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))))))))))))))))))))))))))))) y) →
    (∀ (x y : nat), P x y → Q x) →
    Q (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))))))))))))))))))))))))))))))))))))))

-- ============================================================
-- Induction: add_assoc' (Admitted)
-- ============================================================

-- add_assoc': forall n m p, n + (m + p) = (n + m) + p
axiom Original_LF__DOT__Induction_LF_Induction_add__assoc' :
  ∀ (n m p : nat),
    Corelib_Init_Logic_eq (Nat_add n (Nat_add m p)) (Nat_add (Nat_add n m) p)

-- ============================================================
-- IndProp: inversion_ex2 (Admitted)
-- ============================================================

-- inversion_ex2: forall n, S n = O -> 2 + 2 = 5
axiom Original_LF__DOT__IndProp_LF_IndProp_inversion__ex2 :
  ∀ (n : nat), Corelib_Init_Logic_eq (nat.S n) nat.O → 
    Corelib_Init_Logic_eq (Nat_add (nat.S (nat.S nat.O)) (nat.S (nat.S nat.O))) 
                          (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))

-- ============================================================
-- Logic: leb_plus_exists (Admitted)
-- ============================================================

-- leb_plus_exists: forall n m, n <=? m = true -> exists x, m = n + x
axiom Original_LF__DOT__Logic_LF_Logic_leb__plus__exists :
  ∀ (n m : nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true →
    ex (fun x => Corelib_Init_Logic_eq m (Nat_add n x))
