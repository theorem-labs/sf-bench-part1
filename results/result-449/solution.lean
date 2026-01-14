-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A -> A -> Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat -> nat

def _0 : nat := nat.O
def S : nat -> nat := nat.S

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X -> Original_LF__DOT__Poly_LF_Poly_list X -> Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X -> Original_LF__DOT__Poly_LF_Poly_list X -> Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- trans_eq_example is admitted in Rocq, so we axiomatize it
-- Example trans_eq_example : forall (a b c d e f : nat),
--      [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
axiom Original_LF__DOT__Tactics_LF_Tactics_trans__eq__example :
  forall (a b c d e f : nat),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_nil nat)))
      (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_cons d (Original_LF__DOT__Poly_LF_Poly_nil nat))) ->
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_cons c (Original_LF__DOT__Poly_LF_Poly_cons d (Original_LF__DOT__Poly_LF_Poly_nil nat)))
      (Original_LF__DOT__Poly_LF_Poly_cons e (Original_LF__DOT__Poly_LF_Poly_cons f (Original_LF__DOT__Poly_LF_Poly_nil nat))) ->
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__Poly_LF_Poly_cons a (Original_LF__DOT__Poly_LF_Poly_cons b (Original_LF__DOT__Poly_LF_Poly_nil nat)))
      (Original_LF__DOT__Poly_LF_Poly_cons e (Original_LF__DOT__Poly_LF_Poly_cons f (Original_LF__DOT__Poly_LF_Poly_nil nat)))
