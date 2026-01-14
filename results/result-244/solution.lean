-- Lean translation for examplemap' and dependencies

-- Define our own bool (using a different name to avoid clash with Lean's Bool)
inductive Coqbool : Type where
  | false : Coqbool
  | true : Coqbool

-- Define ascii as 8 bools
inductive Coqascii : Type where
  | Ascii : Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqbool → Coqascii

-- Define string
inductive Coqstring : Type where
  | EmptyString : Coqstring
  | String : Coqascii → Coqstring → Coqstring

-- Aliases for the Checker to use (using a name that can be used)
def String_string := Coqstring

-- Bool equality
def Coqbool_beq (b1 b2 : Coqbool) : Coqbool :=
  match b1, b2 with
  | .true, .true => .true
  | .false, .false => .true
  | _, _ => .false

-- Ascii equality
def Coqascii_eqb (a1 a2 : Coqascii) : Coqbool :=
  match a1, a2 with
  | .Ascii b1 b2 b3 b4 b5 b6 b7 b8, .Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
    match Coqbool_beq b1 c1 with
    | .false => .false
    | .true =>
      match Coqbool_beq b2 c2 with
      | .false => .false
      | .true =>
        match Coqbool_beq b3 c3 with
        | .false => .false
        | .true =>
          match Coqbool_beq b4 c4 with
          | .false => .false
          | .true =>
            match Coqbool_beq b5 c5 with
            | .false => .false
            | .true =>
              match Coqbool_beq b6 c6 with
              | .false => .false
              | .true =>
                match Coqbool_beq b7 c7 with
                | .false => .false
                | .true => Coqbool_beq b8 c8

-- String equality
def Coqstring_eqb : Coqstring → Coqstring → Coqbool
  | .EmptyString, .EmptyString => .true
  | .EmptyString, .String _ _ => .false
  | .String _ _, .EmptyString => .false
  | .String c1 s1, .String c2 s2 =>
    match Coqascii_eqb c1 c2 with
    | .false => .false
    | .true => Coqstring_eqb s1 s2

-- total_map is a function from string to A
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := Coqstring → A

-- t_empty creates a map that always returns v
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update updates a map with a new key-value pair
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} 
    (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : Coqstring) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match Coqstring_eqb x x' with
    | .true => v
    | .false => m x'

-- "foo" = String.String 'f' (String.String 'o' (String.String 'o' EmptyString))
-- 'f' = Ascii false true true false false true true false (102 = 0b01100110)
-- 'o' = Ascii true true true true false true true false (111 = 0b01101111)
def char_f : Coqascii := .Ascii .false .true .true .false .false .true .true .false
def char_o : Coqascii := .Ascii .true .true .true .true .false .true .true .false
def str_foo : Coqstring := .String char_f (.String char_o (.String char_o .EmptyString))

-- "bar" = String.String 'b' (String.String 'a' (String.String 'r' EmptyString))
-- 'b' = Ascii false true false false false true true false (98 = 0b01100010)
-- 'a' = Ascii true false false false false true true false (97 = 0b01100001)
-- 'r' = Ascii false true false false true true true false (114 = 0b01110010)
def char_b : Coqascii := .Ascii .false .true .false .false .false .true .true .false
def char_a : Coqascii := .Ascii .true .false .false .false .false .true .true .false
def char_r : Coqascii := .Ascii .false .true .false .false .true .true .true .false
def str_bar : Coqstring := .String char_b (.String char_a (.String char_r .EmptyString))

-- examplemap' is t_update (t_update (t_empty false) "foo" true) "bar" true
def Original_LF__DOT__Maps_LF_Maps_examplemap' : Coqstring → Coqbool :=
  Original_LF__DOT__Maps_LF_Maps_t__update
    (Original_LF__DOT__Maps_LF_Maps_t__update
      (Original_LF__DOT__Maps_LF_Maps_t__empty Coqbool.false)
      str_foo
      Coqbool.true)
    str_bar
    Coqbool.true
