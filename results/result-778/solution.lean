-- Lean translation for update_example4 and all dependencies
set_option autoImplicit false

-- Bool type (using Coqbool to avoid clash with Lean's Bool)
inductive Coqbool : Type where
  | true : Coqbool
  | false : Coqbool

-- Aliases for bool, true, false
-- Note: we can't use `bool` or `True` directly as they clash with Lean's built-ins
-- So we use Coqbool, Coqbool_true, Coqbool_false and update the isomorphism files accordingly

-- Ascii character: 8 bits
inductive Coqascii : Type where
  | Ascii : Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqascii

def Ascii_ascii := Coqascii
def Ascii_Ascii := Coqascii.Ascii

-- String type
inductive Coqstring : Type where
  | EmptyString : Coqstring
  | String : Coqascii → Coqstring → Coqstring

def String_string := Coqstring
def String_EmptyString := Coqstring.EmptyString
def String_String := Coqstring.String

-- Bool equality
def Bool_eqb (b1 b2 : Coqbool) : Coqbool :=
  match b1, b2 with
  | .true, .true => .true
  | .false, .false => .true
  | _, _ => .false

-- Bool and
def Bool_and (b1 b2 : Coqbool) : Coqbool :=
  match b1 with
  | .true => b2
  | .false => .false

-- Ascii equality
def ascii_eqb (a1 a2 : Coqascii) : Coqbool :=
  match a1, a2 with
  | .Ascii b0 b1 b2 b3 b4 b5 b6 b7, .Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    Bool_and (Bool_eqb b0 c0)
    (Bool_and (Bool_eqb b1 c1)
    (Bool_and (Bool_eqb b2 c2)
    (Bool_and (Bool_eqb b3 c3)
    (Bool_and (Bool_eqb b4 c4)
    (Bool_and (Bool_eqb b5 c5)
    (Bool_and (Bool_eqb b6 c6)
             (Bool_eqb b7 c7)))))))

-- String equality
def String_eqb : Coqstring → Coqstring → Coqbool
  | .EmptyString, .EmptyString => .true
  | .EmptyString, .String _ _ => .false
  | .String _ _, .EmptyString => .false
  | .String c1 s1, .String c2 s2 => Bool_and (ascii_eqb c1 c2) (String_eqb s1 s2)

-- Bool case (if-then-else)
def bool_case (A : Type) (b : Coqbool) (vtrue vfalse : A) : A :=
  match b with
  | .true => vtrue
  | .false => vfalse

-- total_map is a function from string to A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := Coqstring → A

-- t_empty: creates a constant map
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: updates a map at a key
def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : Coqstring) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => bool_case A (String_eqb x x') v (m x')

-- Character definitions
-- 'f' = 102 = 0b01100110 (little endian: false true true false false true true false)
def char_f : Coqascii := .Ascii .false .true .true .false .false .true .true .false
-- 'o' = 111 = 0b01101111 (little endian: true true true true false true true false)
def char_o : Coqascii := .Ascii .true .true .true .true .false .true .true .false
-- 'b' = 98 = 0b01100010 (little endian: false true false false false true true false)
def char_b : Coqascii := .Ascii .false .true .false .false .false .true .true .false
-- 'a' = 97 = 0b01100001 (little endian: true false false false false true true false)
def char_a : Coqascii := .Ascii .true .false .false .false .false .true .true .false
-- 'r' = 114 = 0b01110010 (little endian: false true false false true true true false)
def char_r : Coqascii := .Ascii .false .true .false .false .true .true .true .false

-- String definitions
def str_foo : Coqstring := .String char_f (.String char_o (.String char_o .EmptyString))
def str_bar : Coqstring := .String char_b (.String char_a (.String char_r .EmptyString))

-- examplemap' = ( "bar" !-> true; "foo" !-> true; _ !-> false )
def Original_LF__DOT__Maps_LF_Maps_examplemap' : Coqstring → Coqbool :=
  Original_LF__DOT__Maps_LF_Maps_t__update Coqbool
    (Original_LF__DOT__Maps_LF_Maps_t__update Coqbool
      (Original_LF__DOT__Maps_LF_Maps_t__empty Coqbool Coqbool.false)
      str_foo
      Coqbool.true)
    str_bar
    Coqbool.true

-- Equality type (imports as SProp eq in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality type for Prop arguments
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type
inductive CoqTrue : Prop where
  | intro : CoqTrue

-- Note: we can't use `True` directly as it clashes with Lean's built-in

-- update_example4: examplemap' "bar" = true
-- This is an axiom in Rocq (Admitted), so we declare it as an axiom
axiom Original_LF__DOT__Maps_LF_Maps_update__example4 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Maps_LF_Maps_examplemap' str_bar) Coqbool.true
