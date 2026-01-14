/-
Lean translation for In_app_iff theorem and all dependencies.

Dependencies:
- Original.LF_DOT_Poly.LF.Poly.list
- Original.LF_DOT_Poly.LF.Poly.app
- Original.LF_DOT_Poly.LF.Poly.cons
- Original.LF_DOT_Logic.LF.Logic.In
- Original.False
- iff
- or
- In_app_iff (axiom - Admitted in Original.v)
-/

set_option autoImplicit false

-- Empty inductive type for Original.False (becomes SProp in Rocq)
inductive Original_False : Prop where

-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- Define cons as a definition too (for the cons_iso interface)
def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

-- app function for lists
def Original_LF__DOT__Poly_LF_Poly_app {X : Type} (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app t l2)

-- In predicate: checks if x is in the list (Prop, becomes SProp in Rocq)
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- iff as structure with mp and mpr fields
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- or as a structure with elim field (this allows it to be eliminated to SProp)
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or.inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or.inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- The In_app_iff axiom (Admitted in Original.v)
-- In_app_iff : forall A l l' (a:A), In a (l++l') <-> In a l \/ In a l'.
axiom Original_LF__DOT__Logic_LF_Logic_In__app__iff :
  ∀ (A : Type) (l l' : Original_LF__DOT__Poly_LF_Poly_list A) (a : A),
    iff (Original_LF__DOT__Logic_LF_Logic_In a (Original_LF__DOT__Poly_LF_Poly_app l l'))
        (or (Original_LF__DOT__Logic_LF_Logic_In a l) (Original_LF__DOT__Logic_LF_Logic_In a l'))
