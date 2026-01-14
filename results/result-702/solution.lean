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

-- False proposition  
inductive MyFalse : Prop where

-- Original.False (same as MyFalse)
def Original_False : Prop := MyFalse

-- True proposition
inductive TrueProp : Prop where
  | I : TrueProp

-- Equality in Prop
inductive MyEq (A : Type) : A → A → Prop where
  | refl (a : A) : MyEq A a a

def Corelib_Init_Logic_eq {A : Type} (x y : A) : Prop := MyEq A x y

-- Equality on Prop (for SProp in Rocq)
inductive MyEq_Prop (A : Prop) : A → A → Prop where
  | refl (a : A) : MyEq_Prop A a a

def Corelib_Init_Logic_eq_Prop {A : Prop} (x y : A) : Prop := MyEq_Prop A x y

-- Or type (disjunction)
inductive MyOr (A B : Prop) : Prop where
  | inl : A → MyOr A B
  | inr : B → MyOr A B

-- Logic.not
def Logic_not (P : Prop) : Prop := P → MyFalse

-- In predicate - checks if element is in list
def Original_LF__DOT__Logic_LF_Logic_In {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_list X → Prop
  | Original_LF__DOT__Poly_LF_Poly_list.nil => MyFalse
  | Original_LF__DOT__Poly_LF_Poly_list.cons x' l' => MyOr (Corelib_Init_Logic_eq x' x) (Original_LF__DOT__Logic_LF_Logic_In x l')

-- 42 = S (S (S ... (S 0)...)) - 42 times
def n42 : nat := 
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _0)))))))))))))))))))))))))))))))))))))))))

-- The main theorem: in_not_nil_42_take3 is Admitted in Rocq, so we axiomatize it
-- Lemma in_not_nil_42_take3 : forall l : list nat, In 42 l -> l <> [].
-- The type is: forall l, In 42 l -> l = nil -> False
axiom Original_LF__DOT__Logic_LF_Logic_in__not__nil__42__take3 : ∀ (l : Original_LF__DOT__Poly_LF_Poly_list nat),
  Original_LF__DOT__Logic_LF_Logic_In n42 l →
  Corelib_Init_Logic_eq l (Original_LF__DOT__Poly_LF_Poly_nil nat) → MyFalse
