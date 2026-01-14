-- True - we need to export Lean's built-in True
-- Since we can't redefine it, we create an alias
def MyTrue : Prop := _root_.True
def MyTrue_intro : MyTrue := _root_.True.intro

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also becomes SProp when imported)
-- This is just True since all SProp equalities are trivial
def Corelib_Init_Logic_eq_Prop {A : Prop} (a b : A) : Prop := MyTrue

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- natlist type (custom list of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natlist : Type where
  | nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist
  | cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist

-- natlist constructors
def Original_LF__DOT__Lists_LF_Lists_NatList_nil : Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil

def Original_LF__DOT__Lists_LF_Lists_NatList_cons : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natlist → Original_LF__DOT__Lists_LF_Lists_NatList_natlist :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons

-- natoption type
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- None constructor alias
def Original_LF__DOT__Lists_LF_Lists_NatList_None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

-- Some constructor alias
def Original_LF__DOT__Lists_LF_Lists_NatList_Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some

-- nth_error function
def Original_LF__DOT__Lists_LF_Lists_NatList_nth__error : Original_LF__DOT__Lists_LF_Lists_NatList_natlist → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.nil, _ => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons a _, nat.O => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some a
  | Original_LF__DOT__Lists_LF_Lists_NatList_natlist.cons _ l', nat.S n' => Original_LF__DOT__Lists_LF_Lists_NatList_nth__error l' n'

-- test_nth_error3: nth_error [4;5;6;7] 9 = None
-- [4;5;6;7] is cons 4 (cons 5 (cons 6 (cons 7 nil)))
-- 9 is S (S (S (S (S (S (S (S (S O))))))))
axiom Original_LF__DOT__Lists_LF_Lists_NatList_test__nth__error3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_nth__error
       (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S _0))))
          (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S _0)))))
             (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S (S _0))))))
                (Original_LF__DOT__Lists_LF_Lists_NatList_cons (S (S (S (S (S (S (S _0))))))) Original_LF__DOT__Lists_LF_Lists_NatList_nil))))
       (S (S (S (S (S (S (S (S (S _0))))))))))
    Original_LF__DOT__Lists_LF_Lists_NatList_None
