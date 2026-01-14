-- Define and, or, iff in Prop so they export to SProp in Rocq

-- Custom True that will export as "True" in Rocq
-- We use MyTrue and then manually edit the .out file
inductive MyTrue : Prop where
  | intro : MyTrue

-- and as a structure so it becomes a record with primitive projections
structure and (A B : Prop) : Prop where
  intro ::
  fst : A
  snd : B

-- iff defined in terms of and
def iff (A B : Prop) : Prop := and (A → B) (B → A)

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- andb function
def Original_LF__DOT__Basics_LF_Basics_andb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => b2
  | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Basics_LF_Basics_bool.false

-- The main theorem is admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Logic_LF_Logic_andb__true__iff :
  ∀ (x x0 : Original_LF__DOT__Basics_LF_Basics_bool),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_andb x x0) Original_LF__DOT__Basics_LF_Basics_true)
        (and (Corelib_Init_Logic_eq x Original_LF__DOT__Basics_LF_Basics_true)
             (Corelib_Init_Logic_eq x0 Original_LF__DOT__Basics_LF_Basics_true))
