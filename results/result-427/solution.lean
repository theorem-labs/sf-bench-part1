-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Natural number operations
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => nat_add m (Nat_mul n m)

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons {X : Type} : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- False proposition  
inductive Original_False : Prop where

-- True proposition - named TrueProp to avoid conflict with Lean's True
-- The Rocq file expects Imported.True and Imported.TrueProp_I
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop
inductive eq' (A : Type) : A → A → Prop where
  | refl (a : A) : eq' A a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := eq' A x y

-- Existential quantifier
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : ex P

-- In predicate - checks if element is in list
-- In Rocq: Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
--   match l with
--   | [] => False
--   | x' :: l' => x' = x \/ In x l'
--   end.
def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_False
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => Corelib_Init_Logic_eq x' x ∨ Original_LF__DOT__Logic_LF_Logic_In x l'

-- The main theorem: In_example_2 is Admitted in Rocq, so we axiomatize it
-- Example In_example_2 :
--   forall n, In n [2; 4] ->
--   exists n', n = 2 * n'.
axiom Original_LF__DOT__Logic_LF_Logic_In__example__2 : ∀ (n : nat),
  Original_LF__DOT__Logic_LF_Logic_In n 
    (Original_LF__DOT__Poly_LF_Poly_cons (S (S _0))
      (Original_LF__DOT__Poly_LF_Poly_cons (S (S (S (S _0))))
        (Original_LF__DOT__Poly_LF_Poly_nil nat))) →
  ex (fun n' : nat => Corelib_Init_Logic_eq n (Nat_mul (S (S _0)) n'))
