-- True in Prop (will become SProp in Rocq)
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

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

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- fold definition: folds a function over a list
def Original_LF__DOT__Poly_LF_Poly_fold {X Y : Type} (f : X → Y → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X) (b : Y) : Y :=
  match l with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => b
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => f h (Original_LF__DOT__Poly_LF_Poly_fold f t b)

-- fold_example3 is Admitted in Rocq, so we axiomatize it
-- fold app [[1];[];[2;3];[4]] [] = [1;2;3;4]
axiom Original_LF__DOT__Poly_LF_Poly_fold__example3 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_fold 
      (fun x y => Original_LF__DOT__Poly_LF_Poly_app nat x y)
      (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Poly_LF_Poly_list nat) 
        (Original_LF__DOT__Poly_LF_Poly_cons nat (S _0) (Original_LF__DOT__Poly_LF_Poly_nil nat))
        (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Poly_LF_Poly_list nat)
          (Original_LF__DOT__Poly_LF_Poly_nil nat)
          (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Poly_LF_Poly_list nat)
            (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S _0)) 
              (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S _0))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))
            (Original_LF__DOT__Poly_LF_Poly_cons (Original_LF__DOT__Poly_LF_Poly_list nat)
              (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat))
              (Original_LF__DOT__Poly_LF_Poly_nil (Original_LF__DOT__Poly_LF_Poly_list nat))))))
      (Original_LF__DOT__Poly_LF_Poly_nil nat))
    (Original_LF__DOT__Poly_LF_Poly_cons nat (S _0)
      (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S _0))
        (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S _0)))
          (Original_LF__DOT__Poly_LF_Poly_cons nat (S (S (S (S _0)))) (Original_LF__DOT__Poly_LF_Poly_nil nat)))))
