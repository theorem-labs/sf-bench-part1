-- Polymorphic list type matching Original.LF_DOT_Poly.LF.Poly.list
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- Empty inductive type for False - use Prop so it becomes SProp in Rocq
inductive Original_False : Prop where

-- In predicate: checks if x is in the list
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) (l : Original_LF__DOT__Poly_LF_Poly_list A) : Prop :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => x' = x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- Perm3 inductive type
-- Perm3 relates two lists of exactly 3 elements that are permutations
inductive Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 {X : Type} : 
    Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Prop where
  | perm3_swap12 (a b c : X) : 
      Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 
        (Original_LF__DOT__Poly_LF_Poly_list.cons a (Original_LF__DOT__Poly_LF_Poly_list.cons b (Original_LF__DOT__Poly_LF_Poly_list.cons c Original_LF__DOT__Poly_LF_Poly_list.nil)))
        (Original_LF__DOT__Poly_LF_Poly_list.cons b (Original_LF__DOT__Poly_LF_Poly_list.cons a (Original_LF__DOT__Poly_LF_Poly_list.cons c Original_LF__DOT__Poly_LF_Poly_list.nil)))
  | perm3_swap23 (a b c : X) : 
      Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 
        (Original_LF__DOT__Poly_LF_Poly_list.cons a (Original_LF__DOT__Poly_LF_Poly_list.cons b (Original_LF__DOT__Poly_LF_Poly_list.cons c Original_LF__DOT__Poly_LF_Poly_list.nil)))
        (Original_LF__DOT__Poly_LF_Poly_list.cons a (Original_LF__DOT__Poly_LF_Poly_list.cons c (Original_LF__DOT__Poly_LF_Poly_list.cons b Original_LF__DOT__Poly_LF_Poly_list.nil)))
  | perm3_trans (l1 l2 l3 : Original_LF__DOT__Poly_LF_Poly_list X) : 
      Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 l1 l2 → 
      Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 l2 l3 → 
      Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 l1 l3

-- Perm3_In is an admitted axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_Perm3__In : ∀ (X : Type) (x : X) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X),
  @Original_LF__DOT__IndProp_LF_IndProp_Perm3Reminder_Perm3 X l1 l2 → 
  @Original_LF__DOT__Logic_LF_Logic_In X x l1 → 
  @Original_LF__DOT__Logic_LF_Logic_In X x l2
