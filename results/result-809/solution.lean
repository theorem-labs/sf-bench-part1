-- Lean translation for Original.LF_DOT_Maps.LF.Maps.apply_empty and dependencies

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True as an alias for Lean's True (will be exported to SProp)
def MyTrue : Prop := _root_.True

-- Boolean type (renamed to avoid conflict with Lean's Bool)
inductive MyBool : Type where
  | false : MyBool
  | true : MyBool

-- Ascii character: 8 bits
inductive ascii : Type where
  | Ascii : MyBool → MyBool → MyBool → MyBool → MyBool → MyBool → MyBool → MyBool → ascii

-- String type: list of ascii characters (matching Coq's String.string structure)
inductive String_string : Type where
  | EmptyString : String_string
  | String : ascii → String_string → String_string

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None (A : Type) : option A := option.None

-- total_map is a function type: string -> A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- partial_map is total_map (option A)
def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := 
  Original_LF__DOT__Maps_LF_Maps_total__map (option A)

-- t_empty creates a constant function
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- empty is t_empty None
def Original_LF__DOT__Maps_LF_Maps_empty (A : Type) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__empty (option A) (option.None)

-- apply_empty is an axiom: forall A x, empty A x = None
axiom Original_LF__DOT__Maps_LF_Maps_apply__empty : 
  ∀ (A : Type) (x : String_string), 
    Corelib_Init_Logic_eq (Original_LF__DOT__Maps_LF_Maps_empty A x) (None A)
