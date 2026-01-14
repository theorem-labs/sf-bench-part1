-- True in SProp (will become SProp in Rocq)
inductive MyTrue : Prop where
  | intro : MyTrue

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- negb function
def Original_LF__DOT__Basics_LF_Basics_negb (b : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.true

-- andb function
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- orb function
def Original_LF__DOT__Basics_LF_Basics_orb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false => b2

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- The all3_spec theorem (admitted in Original.v, so axiom here)
-- States: orb (andb b c) (orb (negb b) (negb c)) = true
axiom Original_LF__DOT__Induction_LF_Induction_all3__spec :
  ∀ (b c : Original_LF__DOT__Basics_LF_Basics_bool),
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Basics_LF_Basics_orb
        (Original_LF__DOT__Basics_LF_Basics_andb b c)
        (Original_LF__DOT__Basics_LF_Basics_orb
          (Original_LF__DOT__Basics_LF_Basics_negb b)
          (Original_LF__DOT__Basics_LF_Basics_negb c)))
      Original_LF__DOT__Basics_LF_Basics_true
