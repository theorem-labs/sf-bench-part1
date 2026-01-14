-- Lean 4 translation for restricted_excluded_middle and dependencies

-- True in Prop (will become SProp in Rocq) - named to avoid conflict
inductive MyTrue : Prop where
  | intro : MyTrue

def True_intro : MyTrue := MyTrue.intro

-- False in Prop (will become SProp in Rocq) - named to avoid conflict
inductive MyFalse : Prop where

def False_recl (C : Prop) (H : MyFalse) : C := MyFalse.rec (fun _ => C) H
def False_indl (C : MyFalse → Prop) (H : MyFalse) : C H := MyFalse.rec C H

-- Equality in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

def Corelib_Init_Logic_eq_recl {A : Type} (a : A) (C : A → Prop) (h : C a) (b : A) 
  (H : Corelib_Init_Logic_eq a b) : C b :=
  match H with
  | Corelib_Init_Logic_eq.refl _ => h

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

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

-- The main axiom: restricted_excluded_middle (admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle :
  ∀ (P : Prop) (b : Original_LF__DOT__Basics_LF_Basics_bool),
    iff P (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_true) → 
    or P (P → MyFalse)
