-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Use namespace to avoid conflict with Lean's True
namespace MyDefs
  def True : Prop := TrueProp
end MyDefs

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

-- test_filter_even_gt7_1 is an admitted equality: filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8]
-- Since both filter_even_gt7 and the equality are admitted, we axiomatize the test too
axiom Original_LF__DOT__Poly_LF_Poly_test__filter__even__gt7__1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_filter__even__gt7
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S _0)  -- 1
          (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S _0))  -- 2
             (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))  -- 6
                (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0)))))))))  -- 9
                   (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))  -- 10
                      (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S _0)))  -- 3
                         (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))))  -- 12
                            (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))  -- 8
                               (Original_LF__DOT__Poly_LF_Poly_nil nat))))))))))
    (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))  -- 10
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))))))  -- 12
          (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S _0))))))))  -- 8
             (Original_LF__DOT__Poly_LF_Poly_nil nat))))
