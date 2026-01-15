-- Comprehensive Lean translation for all isomorphism proofs
-- Combines definitions from multiple reference solutions

set_option linter.all false
set_option autoImplicit false

-- ============================================================================
-- Basic Types
-- ============================================================================

-- Define our own nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Aliases
def nat_O := nat.O
def nat_S := nat.S
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Nat operations
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

def nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => nat_sub n m

def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => nat_add m (nat_mul n m)

def nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

def Nat_add := nat_add
def Nat_sub := nat_sub
def Nat_mul := nat_mul
def Nat_pred := nat_pred

def nat_eqb : nat → nat → Bool
  | nat.O, nat.O => true
  | nat.S n, nat.S m => nat_eqb n m
  | _, _ => false

def nat_leb : nat → nat → Bool
  | nat.O, _ => true
  | nat.S _, nat.O => false
  | nat.S n, nat.S m => nat_leb n m

-- ============================================================================
-- Logic types
-- ============================================================================

-- Equality in Prop for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop for Prop arguments  
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True in Prop
namespace Exported
inductive True : Prop where
  | intro : True
end Exported

def TrueType := Exported.True
def TrueType_I := Exported.True.intro

-- False in Prop
namespace Exported
inductive False : Prop where
end Exported

def FalseType := Exported.False

-- And type
structure and (A B : Prop) : Prop where
  intro ::
  left : A
  right : B

-- Logic.not
def Logic_not (P : Prop) : Prop := P → Exported.False

-- ============================================================================
-- Standard bool for isomorphisms
-- ============================================================================

-- mybool type to match names.json expectation
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool_mytrue := mybool.mytrue
def mybool_myfalse := mybool.myfalse

-- ============================================================================
-- Ascii type
-- ============================================================================

inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_ascii_Ascii := Ascii_ascii.Ascii

-- Alias for Ascii.Ascii constructor (for Checker compatibility)
def Ascii_Ascii := Ascii_ascii.Ascii

-- ============================================================================
-- Standard list type
-- ============================================================================

inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def list_nil {A : Type} : list A := list.nil
def list_cons {A : Type} : A → list A → list A := list.cons

-- List In predicate (as a function, matching Rocq Fixpoint In)
def List_In {A : Type} (x : A) : list A → Prop
  | list.nil => Exported.False
  | list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ List_In x l'

-- ============================================================================
-- Standard option type
-- ============================================================================

inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def option_None {A : Type} : option A := option.None
def option_Some {A : Type} : A → option A := option.Some
-- Aliases to match Rocq names
def None {A : Type} : option A := option.None
def Some {A : Type} : A → option A := option.Some

-- ============================================================================
-- LF.Basics types
-- ============================================================================

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb
def Original_LF__DOT__Basics_LF_Basics_negb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- andb
def Original_LF__DOT__Basics_LF_Basics_andb : Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool.true, b => b
  | Original_LF__DOT__Basics_LF_Basics_bool.false, _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- andb3: Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool (Admitted in Original.v)
-- We need to define this properly: andb3 b1 b2 b3 = andb b1 (andb b2 b3)
def Original_LF__DOT__Basics_LF_Basics_andb3 (b1 b2 b3 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_andb b1 (Original_LF__DOT__Basics_LF_Basics_andb b2 b3)

-- test_andb33: andb3 true false true = false (needs to be provable)
def Original_LF__DOT__Basics_LF_Basics_test__andb33 :
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_andb3 Original_LF__DOT__Basics_LF_Basics_true Original_LF__DOT__Basics_LF_Basics_false Original_LF__DOT__Basics_LF_Basics_true)
      Original_LF__DOT__Basics_LF_Basics_false :=
  Corelib_Init_Logic_eq.refl _

-- eqb function (equality test for nat) for Basics
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

-- even
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- plus, mult, exp from Basics
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

def Original_LF__DOT__Basics_LF_Basics_exp : nat → nat → nat
  | base, nat.O => nat.S nat.O
  | base, nat.S p => Original_LF__DOT__Basics_LF_Basics_mult base (Original_LF__DOT__Basics_LF_Basics_exp base p)

-- ============================================================================
-- LF.ProofObjects types
-- ============================================================================

-- ev from ProofObjects
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.S (nat.S n))

-- uncurry (Admitted in Original.v)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_uncurry (P Q R : Prop) (f : P → Q → R) (h : and P Q) : R :=
  f h.left h.right

-- ============================================================================
-- LF.IndPrinciples types  
-- ============================================================================

-- even_ev theorem (Admitted in Original.v)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_even__ev :
  ∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even n) Original_LF__DOT__Basics_LF_Basics_true →
    Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n

-- ============================================================================
-- LF.IndProp types
-- ============================================================================

-- div2
def Original_LF__DOT__IndProp_LF_IndProp_div2 : nat → nat
  | nat.O => nat.O
  | nat.S nat.O => nat.O
  | nat.S (nat.S n') => nat.S (Original_LF__DOT__IndProp_LF_IndProp_div2 n')

-- csf: collatz step function (matches Original definition using nat_mul and nat_add for 3*n+1)
def Original_LF__DOT__IndProp_LF_IndProp_csf (n : nat) : nat :=
  match Original_LF__DOT__Basics_LF_Basics_even n with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__IndProp_LF_IndProp_div2 n
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    nat_add (nat_mul (nat.S (nat.S (nat.S nat.O))) n) (nat.S nat.O)

-- clos_refl_trans
inductive Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y
  | rt_refl (x : X) : Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x x
  | rt_trans (x y z : X) : Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x y →
                           Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R y z →
                           Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans R x z

-- cs: collatz step relation
def Original_LF__DOT__IndProp_LF_IndProp_cs (n m : nat) : Prop :=
  Corelib_Init_Logic_eq (Original_LF__DOT__IndProp_LF_IndProp_csf n) m

-- cms: collatz multi-step (reflexive transitive closure of cs)
def Original_LF__DOT__IndProp_LF_IndProp_cms (n m : nat) : Prop :=
  Original_LF__DOT__IndProp_LF_IndProp_clos__refl__trans Original_LF__DOT__IndProp_LF_IndProp_cs n m

-- ============================================================================
-- LF.Tactics types
-- ============================================================================

-- sillyfun: always returns false
def Original_LF__DOT__Tactics_LF_Tactics_sillyfun (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S nat.O))) with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false =>
    match Original_LF__DOT__Basics_LF_Basics_eqb n (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- sillyfun_false theorem (Admitted in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_sillyfun__false :
  ∀ (n : nat), Corelib_Init_Logic_eq (Original_LF__DOT__Tactics_LF_Tactics_sillyfun n) Original_LF__DOT__Basics_LF_Basics_false

-- ============================================================================
-- LF.Lists types
-- ============================================================================

-- natlist
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

def Original_LF__DOT__Lists_LF_Lists_NatList_nil := Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil
def Original_LF__DOT__Lists_LF_Lists_NatList_cons := Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- app for natlist
def Original_LF__DOT__Lists_LF_Lists_NatList_app : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, l2 => l2
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h t, l2 => Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons h (Original_LF__DOT__Lists_LF_Lists_NatList_app t l2)

-- natoption
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption

def Original_LF__DOT__Lists_LF_Lists_NatList_Some := Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some
def Original_LF__DOT__Lists_LF_Lists_NatList_None := Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

-- id type
inductive Original_LF__DOT__Lists_LF_Lists_id : Type where
  | Id : nat → Original_LF__DOT__Lists_LF_Lists_id

-- eqb_id
def Original_LF__DOT__Lists_LF_Lists_eqb__id : Original_LF__DOT__Lists_LF_Lists_id → Original_LF__DOT__Lists_LF_Lists_id → Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Lists_LF_Lists_id.Id n1, Original_LF__DOT__Lists_LF_Lists_id.Id n2 => Original_LF__DOT__Basics_LF_Basics_eqb n1 n2

-- partial_map
inductive Original_LF__DOT__Lists_LF_Lists_partial__map : Type where
  | empty : Original_LF__DOT__Lists_LF_Lists_partial__map
  | record : Original_LF__DOT__Lists_LF_Lists_id → nat → Original_LF__DOT__Lists_LF_Lists_partial__map → Original_LF__DOT__Lists_LF_Lists_partial__map

-- find
def Original_LF__DOT__Lists_LF_Lists_find (x : Original_LF__DOT__Lists_LF_Lists_id) : Original_LF__DOT__Lists_LF_Lists_partial__map → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | Original_LF__DOT__Lists_LF_Lists_partial__map.empty => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None
  | Original_LF__DOT__Lists_LF_Lists_partial__map.record y v d' =>
    match Original_LF__DOT__Lists_LF_Lists_eqb__id x y with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some v
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Lists_LF_Lists_find x d'

-- update
def Original_LF__DOT__Lists_LF_Lists_update
    (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x : Original_LF__DOT__Lists_LF_Lists_id)
    (value : nat)
    : Original_LF__DOT__Lists_LF_Lists_partial__map :=
  Original_LF__DOT__Lists_LF_Lists_partial__map.record x value d

-- update_neq theorem (Admitted in Original.v)
axiom Original_LF__DOT__Lists_LF_Lists_update__neq :
  ∀ (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x y : Original_LF__DOT__Lists_LF_Lists_id)
    (o : nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_eqb__id x y) Original_LF__DOT__Basics_LF_Basics_false →
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_find x (Original_LF__DOT__Lists_LF_Lists_update d y o)) (Original_LF__DOT__Lists_LF_Lists_find x d)


