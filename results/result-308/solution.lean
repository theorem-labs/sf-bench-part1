-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- andb function
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | .true => b2
  | .false => .false

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Equality type in Prop (will be imported as SProp in Rocq)
inductive Corelib_Init_Logic_eq (A : Type) (x : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq A x x

-- True in Prop - we use MyTrue to avoid conflict with Lean's builtin
-- The Imported.out file will need MyTrue -> True renaming
inductive MyTrue : Prop where
  | intro : MyTrue

-- existsb is admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Tactics_LF_Tactics_existsb : 
  ∀ (X : Type), (X → Original_LF__DOT__Basics_LF_Basics_bool) → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Basics_LF_Basics_bool

-- test_existsb_2 is admitted in Original.v
-- existsb (andb true) [true;true;false] = true
axiom Original_LF__DOT__Tactics_LF_Tactics_test__existsb__2 :
  Corelib_Init_Logic_eq Original_LF__DOT__Basics_LF_Basics_bool
    (Original_LF__DOT__Tactics_LF_Tactics_existsb Original_LF__DOT__Basics_LF_Basics_bool
       (fun x => Original_LF__DOT__Basics_LF_Basics_andb Original_LF__DOT__Basics_LF_Basics_true x)
       (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
             (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
                (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))))
    Original_LF__DOT__Basics_LF_Basics_true
