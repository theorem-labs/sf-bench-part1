-- Lean translation for Original.LF_DOT_Maps.LF.Maps.t_update_permute and dependencies
set_option autoImplicit false

-- Equality in Prop (which imports as SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop types (same structure but for Prop domain)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- False as empty Prop type - use Lean's False
-- We just need an alias for consistent naming
abbrev MyFalse : Prop := False

-- True type - use Lean's True
abbrev MyTrue : Prop := True
def MyTrue_intro : MyTrue := trivial

-- Ascii character: 8 bits
inductive ascii : Type where
  | Ascii : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → ascii

-- String type: list of ascii characters (matching Coq's String.string structure)
inductive String_string : Type where
  | EmptyString : String_string
  | String : ascii → String_string → String_string

-- Option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

-- total_map is a function type: string -> A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- partial_map is total_map (option A)
def Original_LF__DOT__Maps_LF_Maps_partial__map (A : Type) : Type := 
  Original_LF__DOT__Maps_LF_Maps_total__map (option A)

-- String equality (we need this for t_update)
def Bool_eqb (b1 b2 : Bool) : Bool :=
  match b1, b2 with
  | true, true => true
  | false, false => true
  | _, _ => false

def ascii_eqb (a1 a2 : ascii) : Bool :=
  match a1, a2 with
  | ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    Bool_eqb b0 c0 && Bool_eqb b1 c1 && Bool_eqb b2 c2 && Bool_eqb b3 c3 &&
    Bool_eqb b4 c4 && Bool_eqb b5 c5 && Bool_eqb b6 c6 && Bool_eqb b7 c7

def String_eqb : String_string → String_string → Bool
  | String_string.EmptyString, String_string.EmptyString => true
  | String_string.String c1 s1, String_string.String c2 s2 => ascii_eqb c1 c2 && String_eqb s1 s2
  | _, _ => false

-- Bool case analysis (to avoid pulling in Decidable)
def bool_case (A : Type) (b : Bool) (vtrue vfalse : A) : A :=
  match b with
  | true => vtrue
  | false => vfalse

-- t_update: total map update
def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => bool_case A (String_eqb x x') v (m x')

-- update: partial map update (uses t_update with Some v)
def Original_LF__DOT__Maps_LF_Maps_update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__update (option A) m x (option.Some v)

-- Logic.not
def Logic_not (P : Prop) : Prop := P → MyFalse

-- The t_update_permute theorem (axiom since it's Admitted in Rocq)
-- Theorem t_update_permute : forall (A : Type) (m : total_map A) v1 v2 x1 x2,
--   x2 <> x1 ->
--   (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
axiom Original_LF__DOT__Maps_LF_Maps_t__update__permute :
  ∀ (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (v1 v2 : A) (x1 x2 : String_string),
    (Corelib_Init_Logic_eq x2 x1 → MyFalse) →
    Corelib_Init_Logic_eq
      (Original_LF__DOT__Maps_LF_Maps_t__update A 
        (Original_LF__DOT__Maps_LF_Maps_t__update A m x2 v2) x1 v1)
      (Original_LF__DOT__Maps_LF_Maps_t__update A 
        (Original_LF__DOT__Maps_LF_Maps_t__update A m x1 v1) x2 v2)
