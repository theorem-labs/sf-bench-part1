-- Lean translation for test_rev2 and all dependencies

-- True proposition (alias for Lean's built-in True)
def myTrue : Prop := _root_.True
def myTrue_intro : myTrue := _root_.True.intro

-- Equality in Prop for Type (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- true constructor
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors as standalone definitions
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
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_rev X t) (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- test_rev2: rev [true] = [true]
-- This is an Admitted axiom in the original, so we translate it as an axiom
axiom Original_LF__DOT__Poly_LF_Poly_test__rev2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_rev Original_LF__DOT__Basics_LF_Basics_bool
      (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool 
        Original_LF__DOT__Basics_LF_Basics_true 
        (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
    (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool 
      Original_LF__DOT__Basics_LF_Basics_true 
      (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool))
