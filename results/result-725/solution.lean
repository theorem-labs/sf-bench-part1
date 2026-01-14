-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

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

-- filter_even_gt7 is admitted in Rocq, so we axiomatize it
axiom Original_LF__DOT__Poly_LF_Poly_filter__even__gt7 : 
  Original_LF__DOT__Poly_LF_Poly_list nat → Original_LF__DOT__Poly_LF_Poly_list nat

-- test_filter_even_gt7_2 is an admitted equality: filter_even_gt7 [5;2;6;19;129] = []
-- Since both filter_even_gt7 and the equality are admitted, we axiomatize the test too
axiom Original_LF__DOT__Poly_LF_Poly_test__filter__even__gt7__2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter__even__gt7
       (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S _0)))))  -- 5
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))  -- 2
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S _0))))))  -- 6
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))  -- 19
                   (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))  -- 129
                      (Original_LF__DOT__Poly_LF_Poly_nil nat)))))))
    (Original_LF__DOT__Poly_LF_Poly_nil nat)
