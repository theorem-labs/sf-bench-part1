-- Lean translation for update_example3 and all dependencies
set_option autoImplicit false

-- Bool type (using Coqbool to avoid clash with Lean's Bool)
inductive Coqbool : Type where
  | coqtrue : Coqbool
  | coqfalse : Coqbool

def Coqbool_true := Coqbool.coqtrue
def Coqbool_false := Coqbool.coqfalse

-- Alias for bool (we can't use 'bool' directly since Lean already has that)
def mybool := Coqbool

-- Ascii character: 8 bits (using Coqascii to avoid potential clash)
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
def Coqbool_eqb (b1 b2 : Coqbool) : Coqbool :=
  match b1, b2 with
  | .coqtrue, .coqtrue => .coqtrue
  | .coqfalse, .coqfalse => .coqtrue
  | _, _ => .coqfalse

-- Bool and
def Coqbool_and (b1 b2 : Coqbool) : Coqbool :=
  match b1 with
  | .coqtrue => b2
  | .coqfalse => .coqfalse

-- Ascii equality
def Coqascii_eqb (a1 a2 : Coqascii) : Coqbool :=
  match a1, a2 with
  | .Ascii b0 b1 b2 b3 b4 b5 b6 b7, .Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    Coqbool_and (Coqbool_eqb b0 c0)
    (Coqbool_and (Coqbool_eqb b1 c1)
    (Coqbool_and (Coqbool_eqb b2 c2)
    (Coqbool_and (Coqbool_eqb b3 c3)
    (Coqbool_and (Coqbool_eqb b4 c4)
    (Coqbool_and (Coqbool_eqb b5 c5)
    (Coqbool_and (Coqbool_eqb b6 c6)
             (Coqbool_eqb b7 c7)))))))

-- String equality
def Coqstring_eqb : Coqstring → Coqstring → Coqbool
  | .EmptyString, .EmptyString => .coqtrue
  | .EmptyString, .String _ _ => .coqfalse
  | .String _ _, .EmptyString => .coqfalse
  | .String c1 s1, .String c2 s2 => Coqbool_and (Coqascii_eqb c1 c2) (Coqstring_eqb s1 s2)

-- Bool case (if-then-else)
def Coqbool_case (A : Type) (b : Coqbool) (vtrue vfalse : A) : A :=
  match b with
  | .coqtrue => vtrue
  | .coqfalse => vfalse

-- total_map is a function from string to A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := Coqstring → A

-- t_empty: creates a constant map
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: updates a map at a key
def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : Coqstring) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => Coqbool_case A (Coqstring_eqb x x') v (m x')

-- Character definitions
-- 'f' = 102 = 0b01100110 (little endian: false true true false false true true false)
def char_f : Coqascii := .Ascii .coqfalse .coqtrue .coqtrue .coqfalse .coqfalse .coqtrue .coqtrue .coqfalse
-- 'o' = 111 = 0b01101111 (little endian: true true true true false true true false)
def char_o : Coqascii := .Ascii .coqtrue .coqtrue .coqtrue .coqtrue .coqfalse .coqtrue .coqtrue .coqfalse
-- 'b' = 98 = 0b01100010 (little endian: false true false false false true true false)
def char_b : Coqascii := .Ascii .coqfalse .coqtrue .coqfalse .coqfalse .coqfalse .coqtrue .coqtrue .coqfalse
-- 'a' = 97 = 0b01100001 (little endian: true false false false false true true false)
def char_a : Coqascii := .Ascii .coqtrue .coqfalse .coqfalse .coqfalse .coqfalse .coqtrue .coqtrue .coqfalse
-- 'r' = 114 = 0b01110010 (little endian: false true false false true true true false)
def char_r : Coqascii := .Ascii .coqfalse .coqtrue .coqfalse .coqfalse .coqtrue .coqtrue .coqtrue .coqfalse
-- 'q' = 113 = 0b01110001 (little endian: true false false false true true true false)
def char_q : Coqascii := .Ascii .coqtrue .coqfalse .coqfalse .coqfalse .coqtrue .coqtrue .coqtrue .coqfalse
-- 'u' = 117 = 0b01110101 (little endian: true false true false true true true false)
def char_u : Coqascii := .Ascii .coqtrue .coqfalse .coqtrue .coqfalse .coqtrue .coqtrue .coqtrue .coqfalse
-- 'x' = 120 = 0b01111000 (little endian: false false false true true true true false)
def char_x : Coqascii := .Ascii .coqfalse .coqfalse .coqfalse .coqtrue .coqtrue .coqtrue .coqtrue .coqfalse

-- String definitions
def str_foo : Coqstring := .String char_f (.String char_o (.String char_o .EmptyString))
def str_bar : Coqstring := .String char_b (.String char_a (.String char_r .EmptyString))
def str_quux : Coqstring := .String char_q (.String char_u (.String char_u (.String char_x .EmptyString)))

-- examplemap' = ( "bar" !-> true; "foo" !-> true; _ !-> false )
def Original_LF__DOT__Maps_LF_Maps_examplemap' : Coqstring → Coqbool :=
  Original_LF__DOT__Maps_LF_Maps_t__update Coqbool
    (Original_LF__DOT__Maps_LF_Maps_t__update Coqbool
      (Original_LF__DOT__Maps_LF_Maps_t__empty Coqbool Coqbool.coqfalse)
      str_foo
      Coqbool.coqtrue)
    str_bar
    Coqbool.coqtrue

-- Equality type for Type (imports as SProp eq in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality type for Prop (also becomes SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- True type
inductive CoqTrue : Prop where
  | intro : CoqTrue

-- False type (empty proposition)
inductive CoqFalse : Prop where

-- update_example3: examplemap' "quux" = false
-- This is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__Maps_LF_Maps_update__example3 :
  Corelib_Init_Logic_eq (Original_LF__DOT__Maps_LF_Maps_examplemap' str_quux) Coqbool.coqfalse
