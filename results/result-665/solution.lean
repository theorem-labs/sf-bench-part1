-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

-- true constructor
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  .Original_LF__DOT__Basics_LF_Basics_bool_true

-- false constructor
def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  .Original_LF__DOT__Basics_LF_Basics_bool_false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_true

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- cons constructor
def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Equality type in Prop (will be imported as SProp in Rocq)
inductive Corelib_Init_Logic_eq (A : Type) (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq A x x

-- True type in Prop (will be imported as SProp in Rocq)
-- We use True_ and will manually edit the .out file to rename it to True
inductive True_ : Prop where
  | intro : True_

-- forallb function - axiom since it's admitted in Original.v
axiom Original_LF__DOT__Tactics_LF_Tactics_forallb : {X : Type} → (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- test_forallb_2 theorem: forallb negb [false; false] = true
-- This is an admitted theorem in Original.v
axiom Original_LF__DOT__Tactics_LF_Tactics_test__forallb__2 :
  Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Tactics_LF_Tactics_forallb (fun x => Original_LF__DOT__Basics_LF_Basics_negb x)
       (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
             (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool))))
    Original_LF__DOT__Basics_LF_Basics_true
