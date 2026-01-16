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

-- Nat.pred
def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n' => n'

-- Existential quantifier
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

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

-- repeat for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_repeat : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | _, nat.O => .nil
  | n, nat.S count' => .cons n (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n count')

-- rev for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_rev : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | .nil => .nil
  | .cons h t => Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_rev t) (.cons h .nil)

-- nonzeros (Admitted in Original.v, so axiom)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

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

-- contras' (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_contras' :
  ∀ (P : Prop), P → Logic_not P → Corelib_Init_Logic_eq nat.O (nat.S nat.O)

-- ================================================================
-- LF.Lists Theorems (Admitted in Original.v)
-- ================================================================

-- test_app2: nil ++ [4;5] = [4;5]
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__app2 : 
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_app 
       Original_LF__DOT__Lists_LF_Lists_NatList_nil
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil)))
    (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))

-- nonzeros_app (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros__app :
  ∀ (l1 l2 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros (Original_LF__DOT__Lists_LF_Lists_NatList_app l1 l2))
      (Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros l1) (Original_LF__DOT__Lists_LF_Lists_NatList_nonzeros l2))

-- repeat_plus (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_repeat__plus :
  ∀ (c1 c2 n : nat),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n c1) (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n c2))
      (Original_LF__DOT__Lists_LF_Lists_NatList_repeat n (Nat_add c1 c2))

-- rev_app_distr (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_rev__app__distr :
  ∀ (l1 l2 : Original_LF__DOT__Lists_LF_Lists_NatList_natlist),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Lists_LF_Lists_NatList_rev (Original_LF__DOT__Lists_LF_Lists_NatList_app l1 l2))
      (Original_LF__DOT__Lists_LF_Lists_NatList_app (Original_LF__DOT__Lists_LF_Lists_NatList_rev l2) (Original_LF__DOT__Lists_LF_Lists_NatList_rev l1))

-- ================================================================
-- LF.IndProp Theorems (Admitted in Original.v)
-- ================================================================

-- one_not_even (Admitted in Original.v) - using EvPlayground.ev
axiom Original_LF__DOT__IndProp_LF_IndProp_one__not__even :
  Logic_not (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S nat.O))

-- one_not_even' (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_one__not__even' :
  Logic_not (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S nat.O))

-- ================================================================
-- LF.Logic Theorems (Admitted in Original.v)
-- ================================================================

-- dist_not_exists (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_dist__not__exists :
  ∀ (X : Type) (P : X → Prop), (∀ x, P x) → Logic_not (ex (fun x => Logic_not (P x)))

-- not_S_pred_n (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_not__S__pred__n :
  Logic_not (∀ (n : nat), Corelib_Init_Logic_eq (nat.S (Nat_pred n)) n)

-- ================================================================
-- LF.ProofObjects Theorems
-- ================================================================

-- ev_plus4'' (actual definition, not axiom)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4SQUOTESQUOTE (n : nat) (H : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n) : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (Nat_add (nat.S (nat.S (nat.S (nat.S nat.O)))) n) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS (nat.S (nat.S n)) (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n H)
