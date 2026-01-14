-- Lean translation for forallb_true_iff and dependencies

set_option autoImplicit false

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

-- True in Prop (named to match what isomorphism expects)
-- We use Lean's built-in True and just export an alias
def CoqTrue : Prop := True
def CoqTrue_intro : CoqTrue := True.intro

-- Equality in Prop (for SProp import) - Type version
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop (for SProp import) - Prop version  
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- iff in Prop
structure iff (P Q : Prop) : Prop where
  intro ::
  mp : P → Q
  mpr : Q → P

-- forallb is Admitted in Rocq, so axiom here
axiom Original_LF__DOT__Logic_LF_Logic_forallb : 
  {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- All is Admitted in Rocq, so axiom here
axiom Original_LF__DOT__Logic_LF_Logic_All : 
  {T : Type} → (T → Prop) → Original_LF__DOT__Poly_LF_Poly_list T → Prop

-- forallb_true_iff is Admitted in Rocq, so axiom here
axiom Original_LF__DOT__Logic_LF_Logic_forallb__true__iff :
  ∀ (X : Type) (test : X → Original_LF__DOT__Basics_LF_Basics_bool) (l : Original_LF__DOT__Poly_LF_Poly_list X),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Logic_LF_Logic_forallb test l) Original_LF__DOT__Basics_LF_Basics_true)
        (Original_LF__DOT__Logic_LF_Logic_All (fun x => Corelib_Init_Logic_eq (test x) Original_LF__DOT__Basics_LF_Basics_true) l)
