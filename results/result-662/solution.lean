-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq (A : Type) (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq A x x

-- Equality in Prop for Prop arguments (will be exported to SProp)
inductive Corelib_Init_Logic_eq_Prop (A : Prop) (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop A x x

-- True type in Prop (will be imported as SProp in Rocq)
inductive True_ : Prop where
  | intro : True_

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  .Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  .Original_LF__DOT__Basics_LF_Basics_bool_false

-- andb function
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => b2
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_false

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | Original_LF__DOT__Poly_LF_Poly_list_nil : Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list_cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  .Original_LF__DOT__Poly_LF_Poly_list_nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  .Original_LF__DOT__Poly_LF_Poly_list_cons

-- fold function
def Original_LF__DOT__Poly_LF_Poly_fold (X Y : Type) (f : X → Y → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Y → Y
  | .Original_LF__DOT__Poly_LF_Poly_list_nil, b => b
  | .Original_LF__DOT__Poly_LF_Poly_list_cons h t, b => f h (Original_LF__DOT__Poly_LF_Poly_fold X Y f t b)

-- fold_example1: fold andb [true;true;false;true] true = false
-- This is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Poly_LF_Poly_fold__example1 :
  Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Poly_LF_Poly_fold Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool
       (fun x x0 => Original_LF__DOT__Basics_LF_Basics_andb x x0)
       (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
             (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_false
                (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_true
                   (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))))
       Original_LF__DOT__Basics_LF_Basics_true)
    Original_LF__DOT__Basics_LF_Basics_false
