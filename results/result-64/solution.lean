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

-- Predecessor
def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Subtraction
def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n', nat.S m' => Nat_sub n' m'

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

-- Alias for stdlib bool (use mybool to avoid name conflict)
inductive mybool : Type where
  | true : mybool
  | false : mybool

def mybool_true : mybool := mybool.true
def mybool_false : mybool := mybool.false

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

-- orb function
def Original_LF__DOT__Basics_LF_Basics_orb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .true => .true
  | .false => b2

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

-- ============================================================
-- Boolean for le/lt definitions (RocqBool to avoid name collision)
-- ============================================================

-- ============================================================
-- Ascii (8 bools) - using mybool for compatibility with bool_iso
-- ============================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

-- ============================================================
-- String
-- ============================================================

inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

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

-- ============================================================
-- Double (LF.Induction.double)
-- ============================================================

def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- ============================================================
-- EvPlayground.ev (LF.IndProp.EvPlayground.ev)
-- ============================================================

inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → 
            Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

def Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_0 := 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.ev_0
def Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_SS := 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.ev_SS

-- ============================================================
-- Even (LF.Logic.Even) - exists k, n = double k
-- ============================================================

def Original_LF__DOT__Logic_LF_Logic_Even (n : nat) : Prop :=
  ex (fun k => Corelib_Init_Logic_eq n (Original_LF__DOT__Induction_LF_Induction_double k))

-- Successor for le
def le2 (n m : nat) : Prop := le (nat.S n) (nat.S m)

-- lt as Prop
def lt (n m : nat) : Prop := le (nat.S n) m

-- ============================================================
-- Polymorphic list type (LF.Poly.list)
-- ============================================================

-- Alias for stdlib list
inductive mylist (X : Type) : Type where
  | nil : mylist X
  | cons : X → mylist X → mylist X

def mylist_nil (X : Type) : mylist X := mylist.nil
def mylist_cons (X : Type) : X → mylist X → mylist X := mylist.cons

-- List.In for mylist
def List_In {X : Type} (x : X) : mylist X → Prop
  | mylist.nil => MyFalse
  | mylist.cons x' l' => or (Corelib_Init_Logic_eq x' x) (List_In x l')

-- Option type (for stdlib compatibility)
inductive myoption (X : Type) : Type where
  | None : myoption X
  | Some : X → myoption X

def myoption_None (X : Type) : myoption X := myoption.None
def myoption_Some (X : Type) : X → myoption X := myoption.Some

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

-- mylist3: defines a specific natlist [1;2;3]
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist3 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
        Original_LF__DOT__Lists_LF_Lists_NatList_nil))

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
-- Main theorem axioms (Admitted in Original.v)
-- ============================================================

-- test_orb3: orb false true = true (provable by computation)
theorem Original_LF__DOT__Basics_LF_Basics_test__orb3 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_orb Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_true := Corelib_Init_Logic_eq.refl

-- ev_Even (Admitted): forall n, ev n -> Even n
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__Even :
  ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → Original_LF__DOT__Logic_LF_Logic_Even n

-- ev_ev__ev (Admitted): forall n m, ev (n + m) -> ev n -> ev m
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__ev____ev :
  ∀ (n m : nat), 
    Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (Nat_add n m) →
    Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n →
    Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev m

-- add_comm3_take4 (Admitted): forall x y z, x + (y + z) = (z + y) + x
axiom Original_LF__DOT__Logic_LF_Logic_add__comm3__take4 :
  ∀ (x y z : nat), Corelib_Init_Logic_eq (Nat_add x (Nat_add y z)) (Nat_add (Nat_add z y) x)

-- double_neg (Admitted): forall P, P -> ~~P
axiom Original_LF__DOT__Logic_LF_Logic_double__neg :
  ∀ (P : Prop), P → Logic_not (Logic_not P)

-- excluded_middle_irrefutable (Admitted): forall P, ~~(P \/ ~P)
axiom Original_LF__DOT__Logic_LF_Logic_excluded__middle__irrefutable :
  ∀ (P : Prop), Logic_not (Logic_not (or P (Logic_not P)))

-- function_equality_ex1 (Admitted): (fun x => 3 + x) = (fun x => plus 3 x)
axiom Original_LF__DOT__Logic_LF_Logic_function__equality__ex1 :
  Corelib_Init_Logic_eq (fun x : nat => Nat_add (S (S (S _0))) x) (fun x : nat => Original_LF__DOT__Basics_LF_Basics_plus (S (S (S _0))) x)

-- Helper to build large numbers
def nat1001 : nat := Nat_add (Nat_mul (S (S (S (S (S (S (S (S (S (S _0)))))))))) (Nat_mul (S (S (S (S (S (S (S (S (S (S _0)))))))))) (S (S (S (S (S (S (S (S (S (S _0)))))))))))) (S _0)

-- not_even_1001' (Admitted): ~Even 1001
axiom Original_LF__DOT__Logic_LF_Logic_not__even__1001' :
  Logic_not (Original_LF__DOT__Logic_LF_Logic_Even nat1001)

-- plus_exists_leb (Admitted): forall n m, (exists x, m = n+x) -> n <=? m = true
axiom Original_LF__DOT__Logic_LF_Logic_plus__exists__leb :
  ∀ (n m : nat), ex (fun x : nat => Corelib_Init_Logic_eq m (Nat_add n x)) → Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_leb n m) Original_LF__DOT__Basics_LF_Basics_true

-- zero_not_one (Admitted): 0 <> 1
axiom Original_LF__DOT__Logic_LF_Logic_zero__not__one :
  Logic_not (Corelib_Init_Logic_eq _0 (S _0))
