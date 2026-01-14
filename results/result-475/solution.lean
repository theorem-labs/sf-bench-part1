-- Lean 4 translation for orb_true_iff and dependencies

-- True in Prop (will become SProp in Rocq)
-- We export with a workaround name since True is reserved in Lean
inductive MyTrue : Prop where
  | intro : MyTrue

def MyTrue_intro : MyTrue := MyTrue.intro

-- Equality in Prop (will become SProp in Rocq) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

def Corelib_Init_Logic_eq_recl {A : Type} (a : A) (C : A → Prop) (h : C a) (b : A) 
  (H : Corelib_Init_Logic_eq a b) : C b :=
  match H with
  | Corelib_Init_Logic_eq.refl _ => h

-- Equality for Prop/SProp arguments (polymorphic version)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- orb function
def Original_LF__DOT__Basics_LF_Basics_orb (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match b1 with
  | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_bool.false => b2

-- or as a structure with an eliminator field for SProp-compatible elimination
structure or (A B : Prop) : Prop where
  intro ::
  elim : ∀ C : Prop, (A → C) → (B → C) → C

-- Smart constructors for or
def or_inl {A B : Prop} (a : A) : or A B := ⟨fun _ f _ => f a⟩
def or_inr {A B : Prop} (b : B) : or A B := ⟨fun _ _ g => g b⟩

-- iff as conjunction of implications  
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

def iff_mk (A B : Prop) (h1 : A → B) (h2 : B → A) : iff A B := ⟨h1, h2⟩

def mp (A B : Prop) (H : iff A B) : A → B := H.mp
def mpr (A B : Prop) (H : iff A B) : B → A := H.mpr

-- The main axiom: orb_true_iff (admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_orb__true__iff :
  ∀ (b1 b2 : Original_LF__DOT__Basics_LF_Basics_bool),
    iff (Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_orb b1 b2) Original_LF__DOT__Basics_LF_Basics_true)
        (or (Corelib_Init_Logic_eq b1 Original_LF__DOT__Basics_LF_Basics_true) 
            (Corelib_Init_Logic_eq b2 Original_LF__DOT__Basics_LF_Basics_true))
