-- Lean 4 translation for reflect_iff and all dependencies
prelude  -- Disable the prelude to allow redefining True, False, Not

set_option autoImplicit false

-- True (unit type in Prop)
inductive True : Prop where
  | intro : True

-- False (empty type in Prop)  
inductive False : Prop where

-- Not (negation)
def Not (P : Prop) : Prop := P → False

-- iff (biconditional) - structure with mk constructor
structure iff (A B : Prop) : Prop where
  mk ::
  mp : A → B
  mpr : B → A

-- Equality in Type
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Boolean type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- reflect type (matching LF.IndProp.reflect)
-- reflect (P : Prop) : bool -> Prop
inductive Original_LF__DOT__IndProp_LF_IndProp_reflect (P : Prop) : Original_LF__DOT__Basics_LF_Basics_bool → Prop where
  | ReflectT (H : P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.true
  | ReflectF (H : Not P) : Original_LF__DOT__IndProp_LF_IndProp_reflect P Original_LF__DOT__Basics_LF_Basics_bool.false

-- reflect_iff: forall P b, reflect P b -> (P <-> b = true)
-- This is Admitted in Original.v, so we use axiom
axiom Original_LF__DOT__IndProp_LF_IndProp_reflect__iff :
  (P : Prop) → (b : Original_LF__DOT__Basics_LF_Basics_bool) →
    Original_LF__DOT__IndProp_LF_IndProp_reflect P b →
    iff P (Corelib_Init_Logic_eq b Original_LF__DOT__Basics_LF_Basics_true)
