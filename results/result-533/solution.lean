-- Use Lean's built-in True but give it an alias we can export
def myTrue := _root_.True

-- Equality in Prop (will become SProp when imported) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (will become SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- List reverse function
def Original_LF__DOT__Poly_LF_Poly_rev (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_rev X t) (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- pal is an empty inductive proposition indexed by lists (no constructors in the original)
inductive Original_LF__DOT__IndProp_LF_IndProp_pal (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Prop where

-- palindrome_converse is Admitted in the original, so we use an axiom
-- Theorem palindrome_converse : forall {X: Type} (l: list X), l = rev l -> pal l.
axiom Original_LF__DOT__IndProp_LF_IndProp_palindrome__converse : ∀ (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_rev X l) → Original_LF__DOT__IndProp_LF_IndProp_pal X l
