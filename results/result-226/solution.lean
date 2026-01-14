-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Perm3 inductive type (permutations of 3-element lists)
inductive Original_LF__DOT__IndProp_LF_IndProp_Perm3 {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Prop where
  | perm3_swap12 (a b c : X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3
        (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_nil X))))
        (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_nil X))))
  | perm3_swap23 (a b c : X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3
        (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_nil X))))
        (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_nil X))))
  | perm3_trans (l1 l2 l3 : Original_LF__DOT__Poly_LF_Poly_list X) :
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l1 l2 →
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l2 l3 →
      Original_LF__DOT__IndProp_LF_IndProp_Perm3 l1 l3

-- Perm3_ex1 is admitted in Original.v
-- Perm3 [1;2;3] [2;3;1]
axiom Original_LF__DOT__IndProp_LF_IndProp_Perm3__ex1 :
  Original_LF__DOT__IndProp_LF_IndProp_Perm3
    (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0)))
          (Original_LF__DOT__Poly_LF_Poly_cons (S _0) (Original_LF__DOT__Poly_LF_Poly_nil nat))))
