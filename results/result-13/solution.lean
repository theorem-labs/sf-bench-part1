-- Comprehensive Lean translation for all required isomorphisms
-- 
-- MANUAL NAME CHANGES NEEDED IN Imported.out after export:
-- 1. sed -i "s/Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3SQUOTE/Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3'/g" Imported.out
-- 2. sed -i "s/manual__grade__for__no__dup__disjoint__etc/manual__grade__for__NoDup__disjoint__etc/g" Imported.out
--
set_option linter.all false

-- ============================================================
-- Basic Types
-- ============================================================

-- Custom bool to avoid Lean stdlib issues  
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool_mytrue := mybool.mytrue
def mybool_myfalse := mybool.myfalse

-- Legacy aliases for compatibility
def Stdlib_bool := mybool
def Stdlib_bool_true := mybool.mytrue
def Stdlib_bool_false := mybool.myfalse

-- Alias for bool (using Coq_bool to avoid conflict)
def Coq_bool := mybool
def Coq_bool_true := mybool.mytrue
def Coq_bool_false := mybool.myfalse

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Subtraction on nat
def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

-- Multiplication on nat
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

-- Nat equality
def Nat_eqb : nat → nat → mybool
  | nat.O, nat.O => mybool.mytrue
  | nat.S n, nat.S m => Nat_eqb n m
  | _, _ => mybool.myfalse

-- Nat less-than-or-equal
def Nat_leb : nat → nat → mybool
  | nat.O, _ => mybool.mytrue
  | nat.S _, nat.O => mybool.myfalse
  | nat.S n, nat.S m => Nat_leb n m

-- Bool operations
def negb : mybool → mybool
  | mybool.mytrue => mybool.myfalse
  | mybool.myfalse => mybool.mytrue

def andb : mybool → mybool → mybool
  | mybool.mytrue, b => b
  | mybool.myfalse, _ => mybool.myfalse

def orb : mybool → mybool → mybool
  | mybool.mytrue, _ => mybool.mytrue
  | mybool.myfalse, b => b

def Bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

-- Ascii (8-bit character)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    andb (Bool_eqb b0 c0)
      (andb (Bool_eqb b1 c1)
        (andb (Bool_eqb b2 c2)
          (andb (Bool_eqb b3 c3)
            (andb (Bool_eqb b4 c4)
              (andb (Bool_eqb b5 c5)
                (andb (Bool_eqb b6 c6)
                  (Bool_eqb b7 c7)))))))

-- Custom string
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String

-- String equality
def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 =>
    andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- ============================================================
-- Prop-level types
-- ============================================================

-- Equality in Prop (for Type arguments)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl (A : Type) (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop (for Prop arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- MyTrue (maps to Coq's True)
inductive MyTrue : Prop where
  | intro : MyTrue

def MyTrue_intro : MyTrue := MyTrue.intro

-- MyFalse (maps to Coq's False)
inductive MyFalse : Prop where

-- not
def Logic_not (P : Prop) : Prop := P → MyFalse

-- iff
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- ex (existential)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (x : A) (h : P x) : ex P

-- prod
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def prod_pair := @prod.pair

-- option
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None := @option.None
def Some := @option.Some

-- list (stdlib version)
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil := @list.nil
def cons := @list.cons

-- ============================================================
-- Original.LF_DOT_Basics definitions
-- ============================================================

inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- ============================================================
-- Original.LF_DOT_Poly definitions (polymorphic list)
-- ============================================================

inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- option for Poly module
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_Some (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.Some

def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- prod for Poly module
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

def Original_LF__DOT__Poly_LF_Poly_pair (X Y : Type) : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Original_LF__DOT__Poly_LF_Poly_prod.pair

-- partition (Admitted in Original.v - we use an axiom)
axiom Original_LF__DOT__Poly_LF_Poly_partition : {X : Type} → 
  (X → Original_LF__DOT__Basics_LF_Basics_bool) → 
  Original_LF__DOT__Poly_LF_Poly_list X → 
  Original_LF__DOT__Poly_LF_Poly_prod (Original_LF__DOT__Poly_LF_Poly_list X) (Original_LF__DOT__Poly_LF_Poly_list X)

-- test_partition2 (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_test__partition2 : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_partition (fun _ : nat => Original_LF__DOT__Basics_LF_Basics_bool.false) 
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
          (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O Original_LF__DOT__Poly_LF_Poly_list.nil))))
    (Original_LF__DOT__Poly_LF_Poly_prod.pair Original_LF__DOT__Poly_LF_Poly_list.nil
      (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
        (Original_LF__DOT__Poly_LF_Poly_list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
          (Original_LF__DOT__Poly_LF_Poly_list.cons nat.O Original_LF__DOT__Poly_LF_Poly_list.nil))))

-- ============================================================
-- Church numerals (cnat)
-- ============================================================

def Original_LF__DOT__Poly_LF_Poly_Exercises_cnat : Type 1 := 
  (X : Type) → (X → X) → X → X

def Original_LF__DOT__Poly_LF_Poly_Exercises_one : Original_LF__DOT__Poly_LF_Poly_Exercises_cnat :=
  fun (X : Type) (f : X → X) (x : X) => f x

-- one_church_peano (Admitted in Original.v)
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_one__church__peano : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_Exercises_one nat nat.S nat.O) 
    (nat.S nat.O)

-- ============================================================
-- Original.LF_DOT_Maps definitions
-- ============================================================

def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | mybool.mytrue => v
    | mybool.myfalse => m x'

def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := 
  Original_LF__DOT__Maps_LF_Maps_total__map (option A)

def Original_LF__DOT__Maps_LF_Maps_update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__update (option A) m x (option.Some v)

-- update_permute is Admitted in Original.v
axiom Original_LF__DOT__Maps_LF_Maps_update__permute : 
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x1 x2 : String_string) (v1 v2 : A),
    (Corelib_Init_Logic_eq x2 x1 → MyFalse) →
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_update A (Original_LF__DOT__Maps_LF_Maps_update A m x2 v2) x1 v1)
      (Original_LF__DOT__Maps_LF_Maps_update A (Original_LF__DOT__Maps_LF_Maps_update A m x1 v1) x2 v2)

-- ============================================================
-- Original.LF_DOT_Induction definitions
-- ============================================================

def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- ============================================================
-- Original.LF_DOT_Logic definitions
-- ============================================================

def Original_LF__DOT__Logic_LF_Logic_Even (n : nat) : Prop := 
  ex (fun k => Corelib_Init_Logic_eq n (Original_LF__DOT__Induction_LF_Induction_double k))

-- ============================================================
-- Original.LF_DOT_IndProp definitions
-- ============================================================

-- le: less-than-or-equal relation
inductive Original_LF__DOT__IndProp_LF_IndProp_le : nat → nat → Prop where
  | le_n (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n n
  | le_S (n m : nat) : Original_LF__DOT__IndProp_LF_IndProp_le n m → 
      Original_LF__DOT__IndProp_LF_IndProp_le n (nat.S m)

-- ev: even predicate
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS (n : nat) : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → 
      Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev_Even_iff (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__Even__iff : 
  ∀ (n : nat), iff 
    (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n) 
    (Original_LF__DOT__Logic_LF_Logic_Even n)

-- ============================================================
-- Original.LF_DOT_Imp.LF.Imp.AExp definitions
-- ============================================================

-- aexp: arithmetic expressions (in LF.Imp.AExp module)
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus

-- aeval function
def Original_LF__DOT__Imp_LF_Imp_AExp_aeval : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus a1 a2 => 
      Nat_add (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus a1 a2 => 
      Nat_sub (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult a1 a2 => 
      Nat_mul (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)

-- aevalR: relational evaluation (in aevalR_first_try.HypothesisNames module)
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR : 
    Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum (n : nat) : 
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR 
        (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR 
        (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (Nat_add n1 n2)
  | E_AMinus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR 
        (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (Nat_sub n1 n2)
  | E_AMult (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__first__try_HypothesisNames_aevalR 
        (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (Nat_mul n1 n2)

-- ============================================================
-- Maps axioms (Admitted in Original.v)
-- ============================================================

-- t_update_shadow
axiom Original_LF__DOT__Maps_LF_Maps_t__update__shadow :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (x : String_string) (v1 v2 : A),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_t__update A (Original_LF__DOT__Maps_LF_Maps_t__update A m x v1) x v2)
      (Original_LF__DOT__Maps_LF_Maps_t__update A m x v2)

-- t_update_same
axiom Original_LF__DOT__Maps_LF_Maps_t__update__same :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (x : String_string),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_t__update A m x (m x))
      m

-- t_update_permute
axiom Original_LF__DOT__Maps_LF_Maps_t__update__permute :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) (v1 v2 : A) (x1 x2 : String_string),
    (Corelib_Init_Logic_eq x2 x1 → MyFalse) →
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_t__update A (Original_LF__DOT__Maps_LF_Maps_t__update A m x2 v2) x1 v1)
      (Original_LF__DOT__Maps_LF_Maps_t__update A (Original_LF__DOT__Maps_LF_Maps_t__update A m x1 v1) x2 v2)

-- update_shadow
axiom Original_LF__DOT__Maps_LF_Maps_update__shadow :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) (x : String_string) (v1 v2 : A),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_update A (Original_LF__DOT__Maps_LF_Maps_update A m x v1) x v2)
      (Original_LF__DOT__Maps_LF_Maps_update A m x v2)

-- update_neq
-- update_neq: if x2 <> x1 then (x2 |-> v; m) x1 = m x1
axiom Original_LF__DOT__Maps_LF_Maps_update__neq :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) (x1 x2 : String_string) (v : A),
    (Corelib_Init_Logic_eq x2 x1 → MyFalse) →
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Maps_LF_Maps_update A m x2 v x1)
      (m x1)

-- ============================================================
-- Tactics axioms (Admitted in Original.v)
-- ============================================================

-- split_combine_statement (Admitted Definition in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement : Prop

-- split_combine (Admitted proof in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_split__combine : 
  Original_LF__DOT__Tactics_LF_Tactics_split__combine__statement

-- ============================================================
-- AltAuto axioms (Admitted in Original.v)
-- ============================================================

-- match_ex3'
axiom Original_LF__DOT__AltAuto_LF_AltAuto_match__ex3SQUOTE : ∀ (P : Prop), P → P

-- ============================================================
-- IndProp axioms (Admitted in Original.v)
-- ============================================================

-- manual_grade_for_no_dup_disjoint_etc (Definition := None in Original.v)
def Original_LF__DOT__IndProp_LF_IndProp_manual__grade__for__no__dup__disjoint__etc : 
  Original_LF__DOT__Poly_LF_Poly_option (Original_LF__DOT__Poly_LF_Poly_prod nat String_string) := Original_LF__DOT__Poly_LF_Poly_option.None

-- ============================================================
-- Original.LF.Rel definitions
-- ============================================================

def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

def Original_LF_Rel_reflexive (X : Type) (R : Original_LF_Rel_relation X) : Prop :=
  ∀ a : X, R a a

-- le_reflexive (Admitted in Original.v - says reflexive le holds)
axiom Original_LF_Rel_le__reflexive : 
  ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_le n n

-- ============================================================
-- Original.False (different from Prop False)
-- ============================================================

inductive Original_False : Prop where
