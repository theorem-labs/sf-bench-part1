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

-- fold definition: folds a function over a list
def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X) (b : Y) : Y :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => b
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

-- Define plus (addition) on nat
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- Define mult (multiplication) on nat
def Original_LF__DOT__Basics_LF_Basics_mult : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n', m => Original_LF__DOT__Basics_LF_Basics_plus m (Original_LF__DOT__Basics_LF_Basics_mult n' m)

-- fold_example2: fold mult [1;2;3;4] 1 = 24
-- This is Admitted in Rocq, so we axiomatize it
axiom Original_LF__DOT__Poly_LF_Poly_fold__example2 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_fold (fun x x0 : nat => Original_LF__DOT__Basics_LF_Basics_mult x x0)
       (Original_LF__DOT__Poly_LF_Poly_cons (S _0)
          (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
             (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S _0)))
                (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
       (S _0))
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0))))))))))))))))))))))))
