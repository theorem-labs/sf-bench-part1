-- Definitions for nth_error_after_last and its dependencies

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Equality in Prop (will export to SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality on Prop values (will export to SProp in Rocq)
-- This is for when the type parameter is Prop itself
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- MyTrue - will be exported as SProp in Rocq
-- We alias Lean's True
def MyTrue : Prop := _root_.True

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- Option type (matching Original.LF_DOT_Poly.LF.Poly.option)
inductive Original_LF__DOT__Poly_LF_Poly_option (X : Type) : Type where
  | Some : X → Original_LF__DOT__Poly_LF_Poly_option X
  | None : Original_LF__DOT__Poly_LF_Poly_option X

-- None constructor
def Original_LF__DOT__Poly_LF_Poly_None (X : Type) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.None

-- Some constructor
def Original_LF__DOT__Poly_LF_Poly_Some {X : Type} (x : X) : Original_LF__DOT__Poly_LF_Poly_option X :=
  Original_LF__DOT__Poly_LF_Poly_option.Some x

-- Length function
def Original_LF__DOT__Poly_LF_Poly_length {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat
  | Original_LF__DOT__Poly_LF_Poly_list.nil => nat.O
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t => nat.S (Original_LF__DOT__Poly_LF_Poly_length t)

-- nth_error function
def Original_LF__DOT__Poly_LF_Poly_nth__error {X : Type} : Original_LF__DOT__Poly_LF_Poly_list X → nat → Original_LF__DOT__Poly_LF_Poly_option X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, _ => Original_LF__DOT__Poly_LF_Poly_option.None
  | Original_LF__DOT__Poly_LF_Poly_list.cons h _, nat.O => Original_LF__DOT__Poly_LF_Poly_option.Some h
  | Original_LF__DOT__Poly_LF_Poly_list.cons _ t, nat.S n' => Original_LF__DOT__Poly_LF_Poly_nth__error t n'

-- nth_error_after_last is an axiom (Admitted in Original.v)
axiom Original_LF__DOT__Tactics_LF_Tactics_nth__error__after__last :
  ∀ (n : nat) (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_length l) n →
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_nth__error l n) (Original_LF__DOT__Poly_LF_Poly_None X)
