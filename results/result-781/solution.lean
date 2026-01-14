-- Equality in Prop (will be exported to SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (SProp in Rocq for SProp arguments)
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
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- length function
def Original_LF__DOT__Poly_LF_Poly_length {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length t)

-- length_is_1 function: returns true if length of list is 1
def Original_LF__DOT__Poly_LF_Poly_length__is__1 {X : Type} (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_eqb (Original_LF__DOT__Poly_LF_Poly_length l) (nat.S nat.O)

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t =>
    match test h with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- test_filter2: filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ]
-- This is Admitted in Original.v, so we use an axiom here
axiom Original_LF__DOT__Poly_LF_Poly_test__filter2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter (fun x : Original_LF__DOT__Poly_LF_Poly_list nat => Original_LF__DOT__Poly_LF_Poly_length__is__1 x)
       (Original_LF__DOT__Poly_LF_Poly_cons
          (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0)) (Original_LF__DOT__Poly_LF_Poly_nil nat)))
          (Original_LF__DOT__Poly_LF_Poly_cons
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat))
             (Original_LF__DOT__Poly_LF_Poly_cons
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat))
                (Original_LF__DOT__Poly_LF_Poly_cons
                   (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S _0)))))
                      (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S _0))))))
                         (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S _0)))))))
                            (Original_LF__DOT__Poly_LF_Poly_nil nat))))
                   (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Poly_LF_Poly_nil nat)
                      (Original_LF__DOT__Poly_LF_Poly_cons
                         (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S _0))))))))
                            (Original_LF__DOT__Poly_LF_Poly_nil nat))
                         (Original_LF__DOT__Poly_LF_Poly_nil (Original_LF__DOT__Poly_LF_Poly_list nat)))))))))
    (Original_LF__DOT__Poly_LF_Poly_cons
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat))
       (Original_LF__DOT__Poly_LF_Poly_cons
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat))
          (Original_LF__DOT__Poly_LF_Poly_cons
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S _0))))))))
                (Original_LF__DOT__Poly_LF_Poly_nil nat))
             (Original_LF__DOT__Poly_LF_Poly_nil (Original_LF__DOT__Poly_LF_Poly_list nat)))))
