-- Basic types
inductive Original_LF__DOT__Poly_LF_Poly_list (A : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list A
  | cons : A → Original_LF__DOT__Poly_LF_Poly_list A → Original_LF__DOT__Poly_LF_Poly_list A

-- Nat type
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- Logic types
def Original_False : Type := Empty
def Logic_not (P : Type) : Type := P → Original_False
inductive Corelib_Init_Logic_eq (A : Type) (x : A) : A → Type where
  | refl : Corelib_Init_Logic_eq A x x
def Original_True : Type := Unit

-- In predicate
def Original_LF__DOT__Logic_LF_Logic_In {A : Type} (x : A) : Original_LF__DOT__Poly_LF_Poly_list A → Type
  | .nil => Original_False
  | .cons h t => Corelib_Init_Logic_eq A h x ⊕ Original_LF__DOT__Logic_LF_Logic_In x t

-- eqb function for nat
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | .O, .O => .true
  | .O, .S _ => .false
  | .S _, .O => .false
  | .S n, .S m => Original_LF__DOT__Basics_LF_Basics_eqb n m

-- filter function
def Original_LF__DOT__Poly_LF_Poly_filter {X : Type} (test : X → Original_LF__DOT__Basics_LF_Basics_bool) : 
  Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | .nil => .nil
  | .cons h t =>
    match test h with
    | .true => .cons h (Original_LF__DOT__Poly_LF_Poly_filter test t)
    | .false => Original_LF__DOT__Poly_LF_Poly_filter test t

-- The main theorem as an axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_filter__not__empty__In :
  ∀ (n : nat) (l : Original_LF__DOT__Poly_LF_Poly_list nat),
    (Corelib_Init_Logic_eq _ (Original_LF__DOT__Poly_LF_Poly_filter (fun x => Original_LF__DOT__Basics_LF_Basics_eqb n x) l) 
                             (Original_LF__DOT__Poly_LF_Poly_list.nil) → Original_False) →
    Original_LF__DOT__Logic_LF_Logic_In n l