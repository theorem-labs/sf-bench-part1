-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Option type
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

def Original_LF__DOT__Poly_LF_Poly_Some {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.Some

def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- nth_error function
def Original_LF__DOT__Poly_LF_Poly_nth__error {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat → Original_LF__DOT__Poly_LF_Poly_option X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, _ => Original_LF__DOT__Poly_LF_Poly_option.None
  | Original_LF__DOT__Poly_LF_Poly_list.cons a _, nat.O => Original_LF__DOT__Poly_LF_Poly_option.Some a
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t, nat.S n' => Original_LF__DOT__Poly_LF_Poly_nth__error t n'

-- test_nth_error3: nth_error [true] 2 = None
-- The axiom states that the theorem is admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_test__nth__error3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_nth__error
       (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
          (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool))
       (S (S _0)))
    (Original_LF__DOT__Poly_LF_Poly_None Original_LF__DOT__Basics_LF_Basics_bool)

-- list123'' := cons 1 (cons 2 (cons 3 nil)) : list nat
def Original_LF__DOT__Poly_LF_Poly_list123'' : Original_LF__DOT__Poly_LF_Poly_list nat :=
  Original_LF__DOT__Poly_LF_Poly_cons (S _0)
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
      (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0)))
        (Original_LF__DOT__Poly_LF_Poly_nil nat)))
