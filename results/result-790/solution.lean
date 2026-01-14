-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop (exported to SProp -> SProp -> SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type in Prop (will be imported as SProp in Rocq)
inductive True_ : Prop where
  | intro : True_

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | Original_LF__DOT__Basics_LF_Basics_bool_true : Original_LF__DOT__Basics_LF_Basics_bool
  | Original_LF__DOT__Basics_LF_Basics_bool_false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.Original_LF__DOT__Basics_LF_Basics_bool_false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | .Original_LF__DOT__Basics_LF_Basics_bool_true => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | .Original_LF__DOT__Basics_LF_Basics_bool_false => .Original_LF__DOT__Basics_LF_Basics_bool_true

-- even function
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_true
  | nat.S nat.O => .Original_LF__DOT__Basics_LF_Basics_bool_false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- odd function
def Original_LF__DOT__Basics_LF_Basics_odd (n : nat) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_negb (Original_LF__DOT__Basics_LF_Basics_even n)

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- map function
def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | .nil => .nil
  | .cons h t => .cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

-- test_map3: map (fun n => [even n; odd n]) [2;1;2;5] = [[true;false];[false;true];[true;false];[false;true]]
-- This is admitted in Original.v
axiom Original_LF__DOT__Poly_LF_Poly_test__map3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_map
       (fun n => Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Basics_LF_Basics_even n)
          (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Basics_LF_Basics_odd n)
             (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
          (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S _0)))))
                   (Original_LF__DOT__Poly_LF_Poly_nil nat))))))
    (Original_LF__DOT__Poly_LF_Poly_cons
       (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
             (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
       (Original_LF__DOT__Poly_LF_Poly_cons
          (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
             (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
                (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
          (Original_LF__DOT__Poly_LF_Poly_cons
             (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
                (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
                   (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
             (Original_LF__DOT__Poly_LF_Poly_cons
                (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_false
                   (Original_LF__DOT__Poly_LF_Poly_cons Original_LF__DOT__Basics_LF_Basics_true
                      (Original_LF__DOT__Poly_LF_Poly_nil Original_LF__DOT__Basics_LF_Basics_bool)))
                (Original_LF__DOT__Poly_LF_Poly_nil (Original_LF__DOT__Poly_LF_Poly_list Original_LF__DOT__Basics_LF_Basics_bool))))))
