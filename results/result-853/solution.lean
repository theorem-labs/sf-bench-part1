/-
  Lean translation of Imp language definitions for aexp2
  Matches the Rocq definitions exactly for isomorphism checking.
-/

set_option linter.all false

-- Define our own bool type matching Rocq's bool
inductive Coq_bool : Type where
  | Coq_true : Coq_bool
  | Coq_false : Coq_bool

-- Aliases for bool
def mybool := Coq_bool
def mytrue := Coq_bool.Coq_true
def myfalse := Coq_bool.Coq_false

-- Natural numbers matching Rocq's nat
inductive Coq_nat : Type where
  | O : Coq_nat
  | S : Coq_nat → Coq_nat

-- Aliases for nat with proper names  
-- Note: "nat" might conflict; we export Coq_nat and add alias in .out file
def mynat := Coq_nat
def _0 := Coq_nat.O
def S := Coq_nat.S

-- Nat operations
def nat_add : Coq_nat → Coq_nat → Coq_nat
  | Coq_nat.O, m => m
  | Coq_nat.S n, m => Coq_nat.S (nat_add n m)

def nat_sub : Coq_nat → Coq_nat → Coq_nat
  | n, Coq_nat.O => n
  | Coq_nat.O, Coq_nat.S _ => Coq_nat.O
  | Coq_nat.S n, Coq_nat.S m => nat_sub n m

def nat_mul : Coq_nat → Coq_nat → Coq_nat
  | Coq_nat.O, _ => Coq_nat.O
  | Coq_nat.S n, m => nat_add m (nat_mul n m)

def bool_eqb : Coq_bool → Coq_bool → Coq_bool
  | Coq_bool.Coq_true, Coq_bool.Coq_true => Coq_bool.Coq_true
  | Coq_bool.Coq_false, Coq_bool.Coq_false => Coq_bool.Coq_true
  | _, _ => Coq_bool.Coq_false

def bool_andb : Coq_bool → Coq_bool → Coq_bool
  | Coq_bool.Coq_true, b => b
  | Coq_bool.Coq_false, _ => Coq_bool.Coq_false

-- Define Ascii as 8 bools (like Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Coq_bool → Ascii_ascii

-- Define equality on Ascii
def Ascii_eqb : Ascii_ascii → Ascii_ascii → Coq_bool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    bool_andb (bool_eqb b0 c0)
      (bool_andb (bool_eqb b1 c1)
        (bool_andb (bool_eqb b2 c2)
          (bool_andb (bool_eqb b3 c3)
            (bool_andb (bool_eqb b4 c4)
              (bool_andb (bool_eqb b5 c5)
                (bool_andb (bool_eqb b6 c6)
                  (bool_eqb b7 c7)))))))

-- String type (like Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- String equality
def String_eqb : String_string → String_string → Coq_bool
  | String_string.EmptyString, String_string.EmptyString => Coq_bool.Coq_true
  | String_string.String c1 s1, String_string.String c2 s2 =>
    bool_andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => Coq_bool.Coq_false

-- total_map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- t_empty: create empty total map with default value
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- t_update: update a total map
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | Coq_bool.Coq_true => v
    | Coq_bool.Coq_false => m x'

-- State is total_map Coq_nat
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map Coq_nat

-- Helper for building ASCII characters
-- 'X' = 88 = 0b01011000, LSB first: 0,0,0,1,1,0,1,0
def charX : Ascii_ascii := Ascii_ascii.Ascii Coq_bool.Coq_false Coq_bool.Coq_false Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_true Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_false
-- 'Y' = 89 = 0b01011001, LSB first: 1,0,0,1,1,0,1,0
def charY : Ascii_ascii := Ascii_ascii.Ascii Coq_bool.Coq_true Coq_bool.Coq_false Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_true Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_false
-- 'Z' = 90 = 0b01011010, LSB first: 0,1,0,1,1,0,1,0
def charZ : Ascii_ascii := Ascii_ascii.Ascii Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_true Coq_bool.Coq_false Coq_bool.Coq_true Coq_bool.Coq_false

-- Variables X, Y, Z
def Original_LF__DOT__Imp_LF_Imp_X : String_string := String_string.String charX String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Y : String_string := String_string.String charY String_string.EmptyString
def Original_LF__DOT__Imp_LF_Imp_Z : String_string := String_string.String charZ String_string.EmptyString

-- Arithmetic expressions (matches Original.LF_DOT_Imp.LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : Coq_nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Constructor aliases for aexp
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- aeval: evaluates arithmetic expression in a state
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → Coq_nat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- empty_st: the empty state (maps everything to 0)
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  Original_LF__DOT__Maps_LF_Maps_t__empty Coq_nat.O

-- True type as Prop (will be exported as SProp in Rocq)
-- Using "True" would conflict with Lean's True, so we define with prefix
inductive TrueType : Prop where
  | I : TrueType

-- Note: We can't use "True" as it conflicts with Lean's True.
-- The Imported.out will need to be manually edited to add the alias.

-- Equality type in Prop for Type-level equality
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Equality type for Prop-level equality (needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- aexp2: aeval (X !-> 5 ; Y !-> 4) (Z + (X * Y)) = 20
-- State: X = 5, Y = 4, rest = 0
-- Expression: Z + (X * Y) = 0 + (5 * 4) = 0 + 20 = 20
def Original_LF__DOT__Imp_LF_Imp_aexp2 : Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_aeval
       (fun x =>
        Original_LF__DOT__Maps_LF_Maps_t__update
          (fun _ =>
           Original_LF__DOT__Maps_LF_Maps_t__update (fun _ => Original_LF__DOT__Imp_LF_Imp_empty__st x) Original_LF__DOT__Imp_LF_Imp_Y
             (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S Coq_nat.O)))) x)
          Original_LF__DOT__Imp_LF_Imp_X (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S Coq_nat.O))))) x)
       (Original_LF__DOT__Imp_LF_Imp_APlus (Original_LF__DOT__Imp_LF_Imp_AId Original_LF__DOT__Imp_LF_Imp_Z)
          (Original_LF__DOT__Imp_LF_Imp_AMult (Original_LF__DOT__Imp_LF_Imp_AId Original_LF__DOT__Imp_LF_Imp_X)
             (Original_LF__DOT__Imp_LF_Imp_AId Original_LF__DOT__Imp_LF_Imp_Y))))
    (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S (Coq_nat.S Coq_nat.O)))))))))))))))))))) :=
  Corelib_Init_Logic_eq.refl
