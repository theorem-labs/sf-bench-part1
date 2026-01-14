-- Lean translation for eqb_list_true_iff and dependencies

-- Bool type (from LF.Basics)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- List type (from LF.Poly)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- True in Prop (using different name to avoid conflict with Lean's True)
inductive PropTrue : Prop where
  | intro : PropTrue

def PropTrue_intro : PropTrue := PropTrue.intro

-- Equality in Prop (for SProp import)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- iff in Prop
def iff (P Q : Prop) : Prop := (P → Q) ∧ (Q → P)

-- eqb_list function (from LF.Logic) - Admitted in Rocq, so axiom here
axiom Original_LF__DOT__Logic_LF_Logic_eqb__list : 
  {A : Type} → 
  (A → A → Original_LF__DOT__Basics_LF_Basics_bool) → 
  Original_LF__DOT__Poly_LF_Poly_list A → 
  Original_LF__DOT__Poly_LF_Poly_list A → 
  Original_LF__DOT__Basics_LF_Basics_bool

-- eqb_list_true_iff theorem (Admitted in Rocq, so axiom here)
axiom Original_LF__DOT__Logic_LF_Logic_eqb__list__true__iff :
  ∀ (A : Type) (eqb : A → A → Original_LF__DOT__Basics_LF_Basics_bool),
    (∀ a1 a2 : A, iff (Corelib_Init_Logic_eq (eqb a1 a2) Original_LF__DOT__Basics_LF_Basics_true) (Corelib_Init_Logic_eq a1 a2)) →
    ∀ l1 l2 : Original_LF__DOT__Poly_LF_Poly_list A,
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Logic_LF_Logic_eqb__list eqb l1 l2) Original_LF__DOT__Basics_LF_Basics_true)
        (Corelib_Init_Logic_eq l1 l2)
