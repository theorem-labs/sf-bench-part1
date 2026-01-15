-- Comprehensive Lean 4 translation for all needed definitions
set_option linter.unusedVariables false
set_option autoImplicit false

-- ================================================================
-- Basic Logic Types
-- ================================================================

-- Equality in Prop for Type arguments (exported as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (also becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True in Prop (will become SProp when imported in Rocq)
-- Using a namespace to export as "True"
namespace Exported
inductive True : Prop where
  | intro : True
end Exported

def True_intro : Exported.True := Exported.True.intro

-- False in Prop (will become SProp when imported)
-- Using namespace to avoid clash with Lean builtin
namespace Exported
inductive False : Prop where
end Exported

-- And type
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Logic.not
def Logic_not (P : Prop) : Prop := P → Exported.False

-- ================================================================
-- Natural Numbers
-- ================================================================

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

-- ================================================================
-- LF.Basics Boolean Type
-- ================================================================

inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | .true => .false
  | .false => .true

-- even
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => .true
  | nat.S nat.O => .false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- ltb (Admitted in Original.v - so axiom here)
axiom Original_LF__DOT__Basics_LF_Basics_ltb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool

-- test_ltb3: ltb 4 2 = false (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_test__ltb3 :
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Basics_LF_Basics_ltb (S (S (S (S _0)))) (S (S _0)))
    Original_LF__DOT__Basics_LF_Basics_false

-- ================================================================
-- LF.Basics Grade Types
-- ================================================================

inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter := .A
def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter := .B
def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter := .C
def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter := .D
def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter := .F

inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier := .Plus
def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := .Natural
def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier := .Minus

inductive Original_LF__DOT__Basics_LF_Basics_grade : Type where
  | Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade

def Original_LF__DOT__Basics_LF_Basics_Grade : Original_LF__DOT__Basics_LF_Basics_letter → Original_LF__DOT__Basics_LF_Basics_modifier → Original_LF__DOT__Basics_LF_Basics_grade :=
  Original_LF__DOT__Basics_LF_Basics_grade.Grade

inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison := .Eq
def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison := .Lt
def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison := .Gt

-- grade_comparison (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_grade__comparison : 
  Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_grade → Original_LF__DOT__Basics_LF_Basics_comparison

-- test_grade_comparison2 (Admitted in Original.v)
axiom Original_LF__DOT__Basics_LF_Basics_test__grade__comparison2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Basics_LF_Basics_grade__comparison
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Minus)
       (Original_LF__DOT__Basics_LF_Basics_Grade Original_LF__DOT__Basics_LF_Basics_A Original_LF__DOT__Basics_LF_Basics_Plus))
    Original_LF__DOT__Basics_LF_Basics_Lt

-- ================================================================
-- LF.Lists NatList Types
-- ================================================================

inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | .nil, l2 => l2
  | .cons h t, l2 => .cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- test_app1 (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__app1 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S _0)
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S _0))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S _0)))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))))

-- natprod
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

-- fst'
def Original_LF__DOT__Lists_LF_Lists_NatList_fst' (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | .pair x _ => x

-- ================================================================
-- LF.IndProp Types
-- ================================================================

-- div2
def Original_LF__DOT__IndProp_LF_IndProp_div2 : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n) => nat.S (Original_LF__DOT__IndProp_LF_IndProp_div2 n)

-- csf
def Original_LF__DOT__IndProp_LF_IndProp_csf (n : nat) : nat :=
  match Original_LF__DOT__Basics_LF_Basics_even n with
  | .true => Original_LF__DOT__IndProp_LF_IndProp_div2 n
  | .false => Nat_add (Nat_mul (nat.S (nat.S (nat.S nat.O))) n) (nat.S nat.O)

-- cs
def Original_LF__DOT__IndProp_LF_IndProp_cs (n m : nat) : Prop :=
  Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_csf n) m

-- clos_refl_trans
inductive Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step : ∀ x y, R x y → Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y
  | rt_refl : ∀ x, Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x x
  | rt_trans : ∀ x y z, Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y →
                        Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R y z →
                        Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x z

-- cms
def Original_LF__DOT__IndProp_LF_IndProp_cms (n m : nat) : Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans Original_LF__DOT__IndProp_LF_IndProp_cs n m

-- ev from EvPlayground
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

-- ev5_nonsense (Admitted in Original.v) 
axiom Original_LF__DOT__IndProp_LF_IndProp_ev5__nonsense : 
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (S (S (S (S (S _0))))) → 
  Corelib_Init_Logic_eq (Nat_add (S (S _0)) (S (S _0))) (S (S (S (S (S (S (S (S (S _0)))))))))

-- ================================================================
-- LF.ProofObjects Types
-- ================================================================

-- ev from ProofObjects (same structure as EvPlayground.ev but different type)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n))

-- contradiction_implies_anything (Admitted in Original.v)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_contradiction__implies__anything :
  ∀ (P Q : Prop), and P (Logic_not P) → Q

-- ================================================================
-- LF.IndPrinciples Types
-- ================================================================

-- even_ev theorem (Admitted in Original.v)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_even__ev :
  ∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_true → 
    Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n

-- ================================================================
-- LF.AltAuto Types
-- ================================================================

-- auto_example_3 (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__3 :
  ∀ (P Q R S T U : Prop), 
    (P → Q) → (Q → R) → (R → S) → (S → T) → (T → U) → P → U

-- ================================================================
-- LF.Imp.aevalR_division Types
-- ================================================================

-- aexp with division
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | ADiv : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp

-- gt (greater than) for nat
def gt (n m : nat) : Prop := ∃ (k : nat), Corelib_Init_Logic_eq n (Nat_add m (S k))

-- Nat_sub (subtraction)
def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n', nat.S m' => Nat_sub n' m'

-- aevalR relation
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp → nat → Prop where
  | E_ANum (n : nat) : 
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ANum n) n
  | E_APlus (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.APlus a1 a2) (Nat_add n1 n2)
  | E_AMinus (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMinus a1 a2) (Nat_sub n1 n2)
  | E_AMult (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMult a1 a2) (Nat_mul n1 n2)
  | E_ADiv (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 n3 : nat) :
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 →
      gt n2 _0 →
      Corelib_Init_Logic_eq (Nat_mul n2 n3) n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ADiv a1 a2) n3

-- ================================================================
-- LF.Lists.NatList Additional Functions
-- ================================================================

-- hd function
def Original_LF__DOT__Lists_LF_Lists_NatList_hd (default : nat) : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => default
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h _ => h

-- ================================================================
-- LF.Poly Additional Functions
-- ================================================================

-- constfun: returns a constant function
def Original_LF__DOT__Poly_LF_Poly_constfun {X : Type} (x : X) (_n : nat) : X := x

-- constfun_example2: (constfun 5) 99 = 5
theorem Original_LF__DOT__Poly_LF_Poly_constfun__example2 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_constfun (S (S (S (S (S nat.O))))) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S nat.O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S (S (S (S (S nat.O))))) :=
  Corelib_Init_Logic_eq.refl _

-- ================================================================
-- LF.ProofObjects.Props Types
-- ================================================================

-- Props.False (different from Exported.False)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False : Prop where

-- Props.ex (existential)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro (x : A) : P x → Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- ================================================================
-- Additional Theorems (Axioms since they are Admitted in Original.v)
-- ================================================================

-- constructor_example: forall n, ev (n + n) (Admitted in Original.v)
-- Uses EvPlayground.ev, not ProofObjects.ev
axiom Original_LF__DOT__AltAuto_LF_AltAuto_constructor__example :
  ∀ (n : nat), Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (Nat_add n n)

-- implies_to_or: forall P Q, (P -> Q) -> (~P \/ Q)
def Original_LF__DOT__Logic_LF_Logic_implies__to__or : Prop :=
  ∀ (P Q : Prop), (P → Q) → (¬P ∨ Q)

-- ex_ev_Sn: ex (fun n => ev (S n)) (Admitted in Original.v)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun n => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S n))

-- false_implies_zero_eq_one: False -> 0 = 1
def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_false__implies__zero__eq__one :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_False → Corelib_Init_Logic_eq _0 (S _0) :=
  fun contra => nomatch contra

-- ev_4 (IndProp) - Admitted in Original.v
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__4 :
  Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (S (S (S (S _0))))

-- ev_4 (ProofObjects) - Admitted in Original.v
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4 :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S (S (S (S _0))))

-- ev_4' (ProofObjects) - Admitted in Original.v
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4' :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S (S (S (S _0))))

-- ev_4'' (ProofObjects) - Admitted in Original.v
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4'' :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S (S (S (S _0))))

-- ev_4''' (ProofObjects) - Definition in Original.v: ev_SS 2 (ev_SS 0 ev_0)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4''' : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S (S (S (S _0)))) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS (S (S _0)) 
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS _0 
      Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_0)

-- mylist2: definition [1;2;3]
def Original_LF__DOT__Lists_LF_Lists_NatList_mylist2 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (S _0)
    (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (S (S _0))
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (S (S (S _0)))
        Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))

-- odd function (needed for oddmembers)
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match n with
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_odd n'

-- oddmembers: filters odd numbers from a list
def Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t =>
    match Original_LF__DOT__Basics_LF_Basics_odd h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers t

-- test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3]
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__oddmembers :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_oddmembers
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat.O
        (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S nat.O)
          (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat.O
            (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S (nat.S nat.O))
              (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S (nat.S (nat.S nat.O)))
                (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat.O
                  (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons nat.O
                    Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil))))))))
    (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S nat.O)
      (Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons (nat.S (nat.S (nat.S nat.O)))
        Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)) :=
  Corelib_Init_Logic_eq.refl _

-- test_hd2: hd 0 [] = 0
theorem Original_LF__DOT__Lists_LF_Lists_NatList_test__hd2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_hd nat.O Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil)
    nat.O :=
  Corelib_Init_Logic_eq.refl _


