-- Lean translation for Original.LF_DOT_Maps.LF.Maps.examplepmap and dependencies
set_option autoImplicit false

-- Use a namespace to avoid conflict with Lean's Bool
namespace Rocq

-- Bool type 
inductive Bool : Type where
  | true : Bool
  | false : Bool

end Rocq

-- Alias for export - using mybool to avoid conflict, will manually rename to bool in .out
def mybool := Rocq.Bool
def mybool_true := Rocq.Bool.true
def mybool_false := Rocq.Bool.false

-- Ascii character: 8 bits
inductive ascii : Type where
  | Ascii : Rocq.Bool → Rocq.Bool → Rocq.Bool → Rocq.Bool → Rocq.Bool → Rocq.Bool → Rocq.Bool → Rocq.Bool → ascii

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

-- Bool equality
def Bool_eqb (b1 b2 : Rocq.Bool) : Rocq.Bool :=
  match b1, b2 with
  | Rocq.Bool.true, Rocq.Bool.true => Rocq.Bool.true
  | Rocq.Bool.false, Rocq.Bool.false => Rocq.Bool.true
  | _, _ => Rocq.Bool.false

-- Bool and
def Bool_and (b1 b2 : Rocq.Bool) : Rocq.Bool :=
  match b1 with
  | Rocq.Bool.true => b2
  | Rocq.Bool.false => Rocq.Bool.false

-- Ascii equality
def ascii_eqb (a1 a2 : ascii) : Rocq.Bool :=
  match a1, a2 with
  | ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    Bool_and (Bool_eqb b0 c0)
      (Bool_and (Bool_eqb b1 c1)
        (Bool_and (Bool_eqb b2 c2)
          (Bool_and (Bool_eqb b3 c3)
            (Bool_and (Bool_eqb b4 c4)
              (Bool_and (Bool_eqb b5 c5)
                (Bool_and (Bool_eqb b6 c6)
                  (Bool_eqb b7 c7)))))))

-- String equality
def String_eqb : String_string → String_string → Rocq.Bool
  | String_string.EmptyString, String_string.EmptyString => Rocq.Bool.true
  | String_string.String c1 s1, String_string.String c2 s2 => Bool_and (ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => Rocq.Bool.false

-- Bool case analysis
def bool_case (A : Type) (b : Rocq.Bool) (vtrue vfalse : A) : A :=
  match b with
  | Rocq.Bool.true => vtrue
  | Rocq.Bool.false => vfalse

-- t_empty: creates constant function
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: total map update
def Original_LF__DOT__Maps_LF_Maps_t__update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_total__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => bool_case A (String_eqb x x') v (m x')

-- empty: empty partial map
def Original_LF__DOT__Maps_LF_Maps_empty (A : Type) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__empty (option A) (option.None)

-- update: partial map update (uses t_update with Some v)
def Original_LF__DOT__Maps_LF_Maps_update (A : Type) (m : Original_LF__DOT__Maps_LF_Maps_partial__map A) 
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_partial__map A :=
  Original_LF__DOT__Maps_LF_Maps_t__update (option A) m x (option.Some v)

-- Now define the specific strings "Church" and "Turing"
-- ASCII codes use LSB-first encoding like Coq

-- 'C' = 67 = 0b01000011
def ascii_C := ascii.Ascii Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false Rocq.Bool.false Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false

-- 'h' = 104 = 0b01101000
def ascii_h := ascii.Ascii Rocq.Bool.false Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'u' = 117 = 0b01110101
def ascii_u := ascii.Ascii Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'r' = 114 = 0b01110010
def ascii_r := ascii.Ascii Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'c' = 99 = 0b01100011
def ascii_c := ascii.Ascii Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'T' = 84 = 0b01010100
def ascii_T := ascii.Ascii Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false

-- 'i' = 105 = 0b01101001
def ascii_i := ascii.Ascii Rocq.Bool.true Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'n' = 110 = 0b01101110
def ascii_n := ascii.Ascii Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- 'g' = 103 = 0b01100111
def ascii_g := ascii.Ascii Rocq.Bool.true Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false Rocq.Bool.false Rocq.Bool.true Rocq.Bool.true Rocq.Bool.false

-- "Church" string
def string_Church : String_string :=
  String_string.String ascii_C
    (String_string.String ascii_h
      (String_string.String ascii_u
        (String_string.String ascii_r
          (String_string.String ascii_c
            (String_string.String ascii_h
              String_string.EmptyString)))))

-- "Turing" string
def string_Turing : String_string :=
  String_string.String ascii_T
    (String_string.String ascii_u
      (String_string.String ascii_r
        (String_string.String ascii_i
          (String_string.String ascii_n
            (String_string.String ascii_g
              String_string.EmptyString)))))

-- examplepmap := ("Church" |-> true ; "Turing" |-> false)
-- which is: update (update empty "Turing" false) "Church" true
def Original_LF__DOT__Maps_LF_Maps_examplepmap : Original_LF__DOT__Maps_LF_Maps_partial__map Rocq.Bool :=
  Original_LF__DOT__Maps_LF_Maps_update Rocq.Bool
    (Original_LF__DOT__Maps_LF_Maps_update Rocq.Bool
      (Original_LF__DOT__Maps_LF_Maps_empty Rocq.Bool)
      string_Turing
      Rocq.Bool.false)
    string_Church
    Rocq.Bool.true
