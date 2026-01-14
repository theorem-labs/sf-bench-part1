-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive eq' {A : Type} : A → A → Prop where
  | refl (a : A) : eq' a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' x y
def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := eq'.refl a

-- Prop version of eq for when the domain is a Prop
-- This uses Prop as the first argument (becomes SProp in Rocq)
inductive eq'_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : eq'_Prop a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := eq'_Prop x y

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

-- Plus function (matching Rocq definition)
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- Map function for our list type
def Original_LF__DOT__Poly_LF_Poly_map {X Y : Type} (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => Original_LF__DOT__Poly_LF_Poly_list.cons (f h) (Original_LF__DOT__Poly_LF_Poly_map f t)

-- test_map1': map (plus 3) [2;0;2] = [5;3;5]
-- This is admitted in Rocq, so we axiomatize it here
axiom Original_LF__DOT__Poly_LF_Poly_Exercises_test__map1' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_map (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x)
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S nat.O))
          (Original_LF__DOT__Poly_LF_Poly_cons nat.O
             (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S nat.O)) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
    (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))
       (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S nat.O)))
          (Original_LF__DOT__Poly_LF_Poly_cons (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))) (Original_LF__DOT__Poly_LF_Poly_nil nat))))
