-- Comprehensive Lean 4 translation combining all needed definitions
-- This merges definitions from multiple reference solutions
-- 
-- NOTE: After export, run:
--   sed -i "s/Original_LF__DOT__Lists_LF_Lists_NatList_fstSQUOTE/Original_LF__DOT__Lists_LF_Lists_NatList_fst'/g" /workdir/Imported.out
-- This is needed because lean4export converts ' to SQUOTE, but Rocq expects fst'

set_option linter.unusedVariables false
set_option autoImplicit false

-- ================================================================
-- Basic types
-- ================================================================

-- Natural numbers (matching Rocq's nat)
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S' : nat → nat := nat.S
-- Need this alias for Rocq export to get Imported.S
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
| nat.O, m => m
| nat.S p, m => nat.S (Nat_add p m)

-- Multiplication on nat
def Nat_mul : nat → nat → nat
| nat.O, _ => nat.O
| nat.S n', m => Nat_add m (Nat_mul n' m)

-- Subtraction on nat
def Nat_sub : nat → nat → nat
| nat.O, _ => nat.O
| n, nat.O => n
| nat.S n', nat.S m' => Nat_sub n' m'

-- Predecessor
def Nat_pred : nat → nat
| nat.O => nat.O
| nat.S n' => n'

-- Boolean type (matching Rocq bool - using mybool to avoid clash with Lean's Bool)
inductive mybool : Type
| mytrue : mybool
| myfalse : mybool

-- Aliases
def mytrue : mybool := mybool.mytrue
def myfalse : mybool := mybool.myfalse

-- ================================================================
-- LF Basics types
-- ================================================================

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type
| true : Original_LF__DOT__Basics_LF_Basics_bool
| false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- andb
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- orb
def Original_LF__DOT__Basics_LF_Basics_orb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false => b2

-- eqb
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- leb
def Original_LF__DOT__Basics_LF_Basics_leb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O, _ => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_leb n' m'

-- even - standalone implementation using double recursion
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
| nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
| nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
| nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- letter
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type
| A : Original_LF__DOT__Basics_LF_Basics_letter
| B : Original_LF__DOT__Basics_LF_Basics_letter
| C : Original_LF__DOT__Basics_LF_Basics_letter
| D : Original_LF__DOT__Basics_LF_Basics_letter
| F : Original_LF__DOT__Basics_LF_Basics_letter

-- modifier
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type
| Plus : Original_LF__DOT__Basics_LF_Basics_modifier
| Natural : Original_LF__DOT__Basics_LF_Basics_modifier
| Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- grade
inductive Original_LF__DOT__Basics_LF_Basics_grade : Type
| Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

-- comparison
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type
| Eq : Original_LF__DOT__Basics_LF_Basics_comparison
| Lt : Original_LF__DOT__Basics_LF_Basics_comparison
| Gt : Original_LF__DOT__Basics_LF_Basics_comparison

def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Eq

def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Lt

def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison :=
  Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- Bool negation
def negb : mybool → mybool
| mybool.mytrue => mybool.myfalse
| mybool.myfalse => mybool.mytrue

-- Bool conjunction
def andb : mybool → mybool → mybool
| mybool.mytrue, b2 => b2
| mybool.myfalse, _ => mybool.myfalse

-- Bool disjunction
def orb : mybool → mybool → mybool
| mybool.mytrue, _ => mybool.mytrue
| mybool.myfalse, b2 => b2

-- Nat equality
def nat_eqb : nat → nat → mybool
| nat.O, nat.O => mybool.mytrue
| nat.O, nat.S _ => mybool.myfalse
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_eqb n' m'

-- Nat less than or equal
def nat_leb : nat → nat → mybool
| nat.O, _ => mybool.mytrue
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_leb n' m'

-- ================================================================
-- Ascii and String
-- ================================================================

-- Ascii type
inductive Ascii_ascii : Type
| Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii := Ascii_ascii.Ascii

-- String type
inductive String_string : Type
| EmptyString : String_string
| String : Ascii_ascii → String_string → String_string

-- String equality
def mybool_eqb : mybool → mybool → mybool
| mybool.mytrue, mybool.mytrue => mybool.mytrue
| mybool.myfalse, mybool.myfalse => mybool.mytrue
| _, _ => mybool.myfalse

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
| Ascii_ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii_ascii.Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
  match mybool_eqb b1 c1 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue =>
    match mybool_eqb b2 c2 with
    | mybool.myfalse => mybool.myfalse
    | mybool.mytrue =>
      match mybool_eqb b3 c3 with
      | mybool.myfalse => mybool.myfalse
      | mybool.mytrue =>
        match mybool_eqb b4 c4 with
        | mybool.myfalse => mybool.myfalse
        | mybool.mytrue =>
          match mybool_eqb b5 c5 with
          | mybool.myfalse => mybool.myfalse
          | mybool.mytrue =>
            match mybool_eqb b6 c6 with
            | mybool.myfalse => mybool.myfalse
            | mybool.mytrue =>
              match mybool_eqb b7 c7 with
              | mybool.myfalse => mybool.myfalse
              | mybool.mytrue => mybool_eqb b8 c8

def String_eqb : String_string → String_string → mybool
| String_string.EmptyString, String_string.EmptyString => mybool.mytrue
| String_string.String a1 s1, String_string.String a2 s2 =>
  match Ascii_eqb a1 a2 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue => String_eqb s1 s2
| _, _ => mybool.myfalse

-- ================================================================
-- Logic types (will become SProp in Rocq)
-- ================================================================

-- Equality type in Prop
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- Equality for Prop (needed for SProp translation)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

-- True type as Prop (use Lean's built-in True with alias for export)
def True_alias : Prop := True
def True_I : True_alias := True.intro

-- False type as Prop (use Lean's built-in False with alias)
def False_alias : Prop := False

-- not (Logic.not)
def Logic_not (P : Prop) : Prop := P → False_alias

-- and
inductive PandType (A B : Prop) : Prop
| conj : A → B → PandType A B

-- Alias for `and` (exported as Imported.and)
abbrev «and» := PandType

-- or
inductive PorType (A B : Prop) : Prop
| or_introl : A → PorType A B
| or_intror : B → PorType A B

-- iff
def iff (A B : Prop) : Prop := PandType (A → B) (B → A)

-- ex
inductive ex {A : Type} (P : A → Prop) : Prop
| intro : ∀ x : A, P x → ex P

-- le (inductive definition for Prop)
inductive le : nat → nat → Prop
| le_n : ∀ n : nat, le n n
| le_S : ∀ n m : nat, le n m → le n (nat.S m)

-- ================================================================
-- Polymorphic list (for Poly chapter)
-- ================================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type
| nil : Original_LF__DOT__Poly_LF_Poly_list X
| cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
| Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
| Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

def Original_LF__DOT__Poly_LF_Poly_length (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → nat
| Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
| Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length X t)

-- Polymorphic option
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type
| Some : X → Original_LF__DOT__Poly_LF_Poly_option X
| None : Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_Some {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_option X := Original_LF__DOT__Poly_LF_Poly_option.Some x
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X := Original_LF__DOT__Poly_LF_Poly_option.None

-- Polymorphic prod (for Poly chapter)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type
| pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

def Original_LF__DOT__Poly_LF_Poly_pair {X Y : Type} (x : X) (y : Y) : Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Original_LF__DOT__Poly_LF_Poly_prod.pair x y

def Original_LF__DOT__Poly_LF_Poly_fst {X Y : Type} (p : Original_LF__DOT__Poly_LF_Poly_prod X Y) : X :=
  match p with
  | Original_LF__DOT__Poly_LF_Poly_prod.pair x _ => x

def Original_LF__DOT__Poly_LF_Poly_snd {X Y : Type} (p : Original_LF__DOT__Poly_LF_Poly_prod X Y) : Y :=
  match p with
  | Original_LF__DOT__Poly_LF_Poly_prod.pair _ y => y

-- split function
def Original_LF__DOT__Poly_LF_Poly_split {X Y : Type} : Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_prod X Y) →
    Original_LF__DOT__Poly_LF_Poly_prod (Original_LF__DOT__Poly_LF_Poly_list X) (Original_LF__DOT__Poly_LF_Poly_list Y)
| Original_LF__DOT__Poly_LF_Poly_list.nil =>
    Original_LF__DOT__Poly_LF_Poly_prod.pair Original_LF__DOT__Poly_LF_Poly_list.nil Original_LF__DOT__Poly_LF_Poly_list.nil
| Original_LF__DOT__Poly_LF_Poly_list.cons (Original_LF__DOT__Poly_LF_Poly_prod.pair x y) t =>
    let rest := Original_LF__DOT__Poly_LF_Poly_split t
    Original_LF__DOT__Poly_LF_Poly_prod.pair
      (Original_LF__DOT__Poly_LF_Poly_list.cons x (Original_LF__DOT__Poly_LF_Poly_fst rest))
      (Original_LF__DOT__Poly_LF_Poly_list.cons y (Original_LF__DOT__Poly_LF_Poly_snd rest))

-- test_split axiom
axiom Original_LF__DOT__Poly_LF_Poly_test__split :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_split
      (Original_LF__DOT__Poly_LF_Poly_list.cons
        (Original_LF__DOT__Poly_LF_Poly_prod.pair (nat.S nat.O) Original_LF__DOT__Basics_LF_Basics_false)
        (Original_LF__DOT__Poly_LF_Poly_list.cons
          (Original_LF__DOT__Poly_LF_Poly_prod.pair (nat.S (nat.S nat.O)) Original_LF__DOT__Basics_LF_Basics_false)
          Original_LF__DOT__Poly_LF_Poly_list.nil)))
    (Original_LF__DOT__Poly_LF_Poly_prod.pair
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S nat.O)
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S nat.O))
          Original_LF__DOT__Poly_LF_Poly_list.nil))
      (Original_LF__DOT__Poly_LF_Poly_list.cons Original_LF__DOT__Basics_LF_Basics_false
        (Original_LF__DOT__Poly_LF_Poly_list.cons Original_LF__DOT__Basics_LF_Basics_false
          Original_LF__DOT__Poly_LF_Poly_list.nil)))

-- Option/option alias for the standard checker
inductive myoption (A : Type) : Type
| mySome : A → myoption A
| myNone : myoption A

def mySome {A : Type} (x : A) : myoption A := myoption.mySome x
def myNone (A : Type) : myoption A := myoption.myNone

-- Alias for option checker
abbrev option := myoption
def option_Some {A : Type} (x : A) : option A := myoption.mySome x
def option_None (A : Type) : option A := myoption.myNone

-- ================================================================
-- Prod type
-- ================================================================

inductive myprod (A B : Type) : Type
| mk : A → B → myprod A B

-- Alias for prod checker
abbrev prod := myprod
def prod_mk {A B : Type} (a : A) (b : B) : prod A B := myprod.mk a b

-- ================================================================
-- NatList (from Lists chapter)
-- ================================================================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type
| nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
| cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons (n : nat) (l : Original_LF__DOT__Lists_LF_Lists_NatList_natlist) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons n l

-- nonzeros function for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
| Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
| Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat.O t => Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros t
| Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros t)

-- test_nonzeros axiom
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__nonzeros :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
            (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
              (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
                  (Original_LF__DOT__Lists_LF_Lists_NatList_cons nat.O
                    Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))))))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S nat.O)
      (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S nat.O))
        (Original_LF__DOT__Lists_LF_Lists_NatList_cons (nat.S (nat.S (nat.S nat.O)))
          Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)))

-- ================================================================
-- Standard list (for stdlib list checker)
-- ================================================================

inductive mylist (A : Type) : Type
| mynil : mylist A
| mycons : A → mylist A → mylist A

def mynil (A : Type) : mylist A := mylist.mynil
def mycons {A : Type} (x : A) (l : mylist A) : mylist A := mylist.mycons x l
def mylist_nil (A : Type) : mylist A := mylist.mynil
def mylist_cons (A : Type) (x : A) (l : mylist A) : mylist A := mylist.mycons x l

-- List.In for compatibility
inductive List_In {A : Type} (x : A) : mylist A → Prop
| here : ∀ l : mylist A, List_In x (mylist.mycons x l)
| there : ∀ y l, List_In x l → List_In x (mylist.mycons y l)

-- ================================================================
-- Maps (total_map and partial_map)
-- ================================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
            | mybool.mytrue => v
            | mybool.myfalse => m x'

def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := Original_LF__DOT__Maps_LF_Maps_total__map (myoption A)

-- ================================================================
-- Imp types
-- ================================================================

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- empty_st
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  fun _ => nat.O

-- X, Y, Z variable definitions
-- 'X' = 88 = 01011000, bits: b0=0,b1=0,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- 'Y' = 89 = 01011001, bits: b0=1,b1=0,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_Y : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- 'Z' = 90 = 01011010, bits: b0=0,b1=1,b2=0,b3=1,b4=1,b5=0,b6=1,b7=0
def Original_LF__DOT__Imp_LF_Imp_Z : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.mytrue mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type
| ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
| AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
| APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

def Original_LF__DOT__Imp_LF_Imp_ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type
| BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
| BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
| BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

def Original_LF__DOT__Imp_LF_Imp_BTrue : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- com (commands)
inductive Original_LF__DOT__Imp_LF_Imp_com : Type
| CSkip : Original_LF__DOT__Imp_LF_Imp_com
| CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
| CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
| CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
| CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

def Original_LF__DOT__Imp_LF_Imp_CSkip : Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSkip
def Original_LF__DOT__Imp_LF_Imp_CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CAsgn
def Original_LF__DOT__Imp_LF_Imp_CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CSeq
def Original_LF__DOT__Imp_LF_Imp_CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CIf
def Original_LF__DOT__Imp_LF_Imp_CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com := Original_LF__DOT__Imp_LF_Imp_com.CWhile

-- aeval
def Original_LF__DOT__Imp_LF_Imp_aeval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_aexp →
    nat
| _st, Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
| st, Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 =>
    Nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 =>
    Nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 =>
    Nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- beval
def Original_LF__DOT__Imp_LF_Imp_beval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_bexp →
    mybool
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => mybool.mytrue
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => mybool.myfalse
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 =>
    nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 =>
    negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 =>
    nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 =>
    negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 =>
    negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 =>
    andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- ================================================================
-- Rel types
-- ================================================================

def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- transitive relation property
def Original_LF_Rel_transitive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

def Original_LF_Rel_antisymmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a → Corelib_Init_Logic_eq a b

def Original_LF_Rel_reflexive {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a : X, R a a

def Original_LF_Rel_symmetric {X : Type} (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a b : X, R a b → R b a

-- ================================================================
-- Logic In
-- ================================================================

inductive Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Prop
| here : ∀ l : Original_LF__DOT__Poly_LF_Poly_list A, Original_LF__DOT__Logic_LF_Logic_In x (Original_LF__DOT__Poly_LF_Poly_list.cons x l)
| there : ∀ y l, Original_LF__DOT__Logic_LF_Logic_In x l → Original_LF__DOT__Logic_LF_Logic_In x (Original_LF__DOT__Poly_LF_Poly_list.cons y l)

-- ================================================================
-- ImpCEvalFun manual_grade_for_ceval_step__ceval_inf
-- ================================================================

def Original_LF__DOT__ImpCEvalFun_LF_ImpCEvalFun_manual__grade__for__ceval__step____ceval__inf : myoption (myprod nat String_string) := myoption.myNone

-- app_length' axiom
axiom Original_LF__DOT__AltAuto_LF_AltAuto_app__length' : ∀ (X : Type) (lst1 lst2 : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_length X (Original_LF__DOT__Poly_LF_Poly_app X lst1 lst2))
    (Nat_add (Original_LF__DOT__Poly_LF_Poly_length X lst1) (Original_LF__DOT__Poly_LF_Poly_length X lst2))

-- modifier_comparison
def Original_LF__DOT__Basics_LF_Basics_modifier__comparison (m1 m2 : Original_LF__DOT__Basics_LF_Basics_modifier) : Original_LF__DOT__Basics_LF_Basics_comparison :=
  match m1, m2 with
  | Original_LF__DOT__Basics_LF_Basics_modifier.Plus, Original_LF__DOT__Basics_LF_Basics_modifier.Plus => Original_LF__DOT__Basics_LF_Basics_comparison.Eq
  | Original_LF__DOT__Basics_LF_Basics_modifier.Plus, _ => Original_LF__DOT__Basics_LF_Basics_comparison.Gt
  | Original_LF__DOT__Basics_LF_Basics_modifier.Natural, Original_LF__DOT__Basics_LF_Basics_modifier.Plus => Original_LF__DOT__Basics_LF_Basics_comparison.Lt
  | Original_LF__DOT__Basics_LF_Basics_modifier.Natural, Original_LF__DOT__Basics_LF_Basics_modifier.Natural => Original_LF__DOT__Basics_LF_Basics_comparison.Eq
  | Original_LF__DOT__Basics_LF_Basics_modifier.Natural, _ => Original_LF__DOT__Basics_LF_Basics_comparison.Gt
  | Original_LF__DOT__Basics_LF_Basics_modifier.Minus, Original_LF__DOT__Basics_LF_Basics_modifier.Minus => Original_LF__DOT__Basics_LF_Basics_comparison.Eq
  | Original_LF__DOT__Basics_LF_Basics_modifier.Minus, _ => Original_LF__DOT__Basics_LF_Basics_comparison.Lt

-- plus
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
| nat.O, m => m
| nat.S p, m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus p m)

-- mult
def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
| nat.O, _ => nat.O
| nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

-- exp
def Original_LF__DOT__Basics_LF_Basics_exp : nat → nat → nat
| _, nat.O => nat.S nat.O
| base, nat.S p' => Original_LF__DOT__Basics_LF_Basics_mult base (Original_LF__DOT__Basics_LF_Basics_exp base p')

-- ================================================================
-- Lists.NatList.natprod
-- ================================================================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type
| pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

def Original_LF__DOT__Lists_LF_Lists_NatList_natprod_pair := Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair

def Original_LF__DOT__Lists_LF_Lists_NatList_fst (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x

def Original_LF__DOT__Lists_LF_Lists_NatList_snd (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair _ y => y

-- fst' is the same as fst for natprod
def Original_LF__DOT__Lists_LF_Lists_NatList_fstSQUOTE (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x

-- ================================================================
-- ProofObjects.ev
-- ================================================================

inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop
| ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O
| ev_SS : ∀ (n : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n))

def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev__0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_0

def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_ev__SS (n : nat) (h : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n) : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n)) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n h

-- ================================================================
-- ProofObjects.Props.ex
-- ================================================================

inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A → Prop) : Prop
| ex_intro : ∀ (x : A), P x → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- some_nat_is_even : ev 4
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even : Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex Original_LF__DOT__ProofObjects_LF_ProofObjects_ev :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro
    (nat.S (nat.S (nat.S (nat.S nat.O))))
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS (nat.S (nat.S nat.O))
      (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS nat.O Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_0))

-- ================================================================
-- Poly.MumbleGrumble
-- ================================================================

inductive Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble : Type
| a : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble
| b : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble → nat → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble
| c : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble

inductive Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble (X : Type) : Type
| d : Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_mumble → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X
| e : X → Original_LF__DOT__Poly_LF_Poly_MumbleGrumble_grumble X

-- ================================================================
-- Logic theorems
-- ================================================================

-- not_both_true_and_false axiom
axiom Original_LF__DOT__Logic_LF_Logic_not__both__true__and__false : ∀ (P : Prop), Logic_not (PandType P (Logic_not P))

-- contrapositive (admitted in original)
axiom Original_LF__DOT__Logic_LF_Logic_contrapositive : ∀ (P Q : Prop), (P → Q) → (Logic_not Q → Logic_not P)

-- match_ex4 (admitted in original)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_match__ex4 : ∀ (P Q : Prop), P → Q → P

-- plus_eqb_example axiom  
axiom Original_LF__DOT__Logic_LF_Logic_plus__eqb__example : ∀ (n m p : nat),
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb n m) Original_LF__DOT__Basics_LF_Basics_true →
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_eqb (Nat_add n p) (Nat_add m p)) Original_LF__DOT__Basics_LF_Basics_true
