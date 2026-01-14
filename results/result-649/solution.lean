/-!
  Lean translation for even_bool_prop and its dependencies.
  
  We need to export:
  - nat (isomorphic to Rocq nat)
  - True (for SProp True)
  - Corelib_Init_Logic_eq (isomorphic to Rocq equality in SProp)
  - Original_LF__DOT__Basics_LF_Basics_bool (the bool type)
  - Original_LF__DOT__Basics_LF_Basics_true (the true constructor)
  - Original_LF__DOT__Basics_LF_Basics_false (the false constructor)
  - Original_LF__DOT__Basics_LF_Basics_even (the even function)
  - Original_LF__DOT__Induction_LF_Induction_double (the double function)
  - iff (the biconditional)
  - Original_LF__DOT__Logic_LF_Logic_Even (exists n, x = double n)
  - Original_LF__DOT__Logic_LF_Logic_even__bool__prop (the axiom)
-/

-- Define our own nat to avoid issues with Lean's Nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Alias for True - use MyTrue to avoid collision
def MyTrue : Prop := _root_.True

def MyTrue_intro : MyTrue := _root_.True.intro

-- Define equality in Prop (will be mapped to SProp in Rocq) - for Type arguments
inductive Corelib_Init_Logic_eq {α : Type} (a : α) : α → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {α : Type} (a : α) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Define equality in Prop for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {α : Prop} (a : α) : α → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {α : Prop} (a : α) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- Define the even function (matching the Rocq definition)
def Original_LF__DOT__Basics_LF_Basics_even : nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.S nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S (nat.S n') => Original_LF__DOT__Basics_LF_Basics_even n'

-- Define double function on nat (matching the Rocq definition)
def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- iff as a structure so it becomes a record with primitive projections
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- Existential for Even (specialized to nat -> Prop)
inductive Original_LF__DOT__Logic_LF_Logic_Even_ex (P : nat -> Prop) : Prop where
  | intro : (x : nat) -> P x -> Original_LF__DOT__Logic_LF_Logic_Even_ex P

-- Even definition: exists n, x = double n
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  Original_LF__DOT__Logic_LF_Logic_Even_ex (fun n => Corelib_Init_Logic_eq x (Original_LF__DOT__Induction_LF_Induction_double n))

-- The theorem even_bool_prop as an axiom (it's Admitted in the original)
-- Theorem even_bool_prop : forall n, even n = true <-> Even n.
axiom Original_LF__DOT__Logic_LF_Logic_even__bool__prop :
  ∀ (x : nat),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_even x) Original_LF__DOT__Basics_LF_Basics_true)
        (Original_LF__DOT__Logic_LF_Logic_Even x)
