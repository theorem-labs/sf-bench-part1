-- Lean 4 translation for bexp1 and all dependencies

set_option linter.unusedVariables false
set_option autoImplicit false

-- Boolean type (matching Rocq bool)  
inductive mybool : Type
| mytrue : mybool
| myfalse : mybool

-- Aliases
def mytrue : mybool := mybool.mytrue
def myfalse : mybool := mybool.myfalse

-- Type-level alias for bool checker
def bool' : Type := mybool
def true' : mybool := mybool.mytrue

-- Natural numbers
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Ascii type
inductive Ascii_ascii : Type
| Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- String type
inductive String_string : Type
| EmptyString : String_string
| String : Ascii_ascii → String_string → String_string

-- Total map type
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- t_empty for total_map
def Original_LF__DOT__Maps_LF_Maps_t__empty {A : Type} (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- String equality function
def mybool_eqb : mybool → mybool → mybool
| mybool.mytrue, mybool.mytrue => mybool.mytrue
| mybool.myfalse, mybool.myfalse => mybool.mytrue
| _, _ => mybool.myfalse

def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
| Ascii_ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8, Ascii_ascii.Ascii c1 c2 c3 c4 c5 c6 c7 c8 =>
  match mybool_eqb b1 c1 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue =>
    match mybool_eqb b2 c2 with
    | mybool.myfalse => mybool.myfalse
    | mybool.mytrue =>
      match mybool_eqb b3 c3 with
      | mybool.myfalse => mybool.myfalse
      | mybool.mytrue =>
        match mybool_eqb b4 c4 with
        | mybool.myfalse => mybool.myfalse
        | mybool.mytrue =>
          match mybool_eqb b5 c5 with
          | mybool.myfalse => mybool.myfalse
          | mybool.mytrue =>
            match mybool_eqb b6 c6 with
            | mybool.myfalse => mybool.myfalse
            | mybool.mytrue =>
              match mybool_eqb b7 c7 with
              | mybool.myfalse => mybool.myfalse
              | mybool.mytrue => mybool_eqb b8 c8

def String_eqb : String_string → String_string → mybool
| String_string.EmptyString, String_string.EmptyString => mybool.mytrue
| String_string.String a1 s1, String_string.String a2 s2 =>
  match Ascii_eqb a1 a2 with
  | mybool.myfalse => mybool.myfalse
  | mybool.mytrue => String_eqb s1 s2
| _, _ => mybool.myfalse

-- t_update for total_map
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
            | mybool.mytrue => v
            | mybool.myfalse => m x'

-- empty_st: state that maps everything to 0
def Original_LF__DOT__Imp_LF_Imp_empty__st : Original_LF__DOT__Imp_LF_Imp_state :=
  fun _ => nat.O

-- X variable definition: "X" as an ASCII string
-- 'X' in ASCII is 88 = 01011000
-- In Coq's Ascii, the bit order is b0 b1 b2 b3 b4 b5 b6 b7 where b0 is LSB
-- 88 = 64 + 16 + 8 = 2^6 + 2^4 + 2^3
-- So bits: b0=0, b1=0, b2=0, b3=1, b4=1, b5=0, b6=1, b7=0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- Define aexp
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type
| ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
| AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
| APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
| AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Export aexp constructors
def Original_LF__DOT__Imp_LF_Imp_ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Define bexp
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type
| BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
| BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
| BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
| BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- Export bexp constructors
def Original_LF__DOT__Imp_LF_Imp_BTrue : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
def Original_LF__DOT__Imp_LF_Imp_BFalse : Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BFalse
def Original_LF__DOT__Imp_LF_Imp_BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BEq
def Original_LF__DOT__Imp_LF_Imp_BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNeq
def Original_LF__DOT__Imp_LF_Imp_BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BLe
def Original_LF__DOT__Imp_LF_Imp_BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BGt
def Original_LF__DOT__Imp_LF_Imp_BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BNot
def Original_LF__DOT__Imp_LF_Imp_BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp := Original_LF__DOT__Imp_LF_Imp_bexp.BAnd

-- Nat operations
def nat_add : nat → nat → nat
| nat.O, m => m
| nat.S n', m => nat.S (nat_add n' m)

def nat_sub : nat → nat → nat
| nat.O, _ => nat.O
| n, nat.O => n
| nat.S n', nat.S m' => nat_sub n' m'

def nat_mul : nat → nat → nat
| nat.O, _ => nat.O
| nat.S n', m => nat_add m (nat_mul n' m)

-- Nat comparison: equality
def nat_eqb : nat → nat → mybool
| nat.O, nat.O => mybool.mytrue
| nat.O, nat.S _ => mybool.myfalse
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_eqb n' m'

-- Nat comparison: less than or equal
def nat_leb : nat → nat → mybool
| nat.O, _ => mybool.mytrue
| nat.S _, nat.O => mybool.myfalse
| nat.S n', nat.S m' => nat_leb n' m'

-- Bool negation
def negb : mybool → mybool
| mybool.mytrue => mybool.myfalse
| mybool.myfalse => mybool.mytrue

-- Bool conjunction
def andb : mybool → mybool → mybool
| mybool.mytrue, b2 => b2
| mybool.myfalse, _ => mybool.myfalse

-- Define aeval
def Original_LF__DOT__Imp_LF_Imp_aeval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_aexp →
    nat
| _st, Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
| st, Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 =>
    nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 =>
    nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 =>
    nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- Define beval
def Original_LF__DOT__Imp_LF_Imp_beval :
    (String_string → nat) →
    Original_LF__DOT__Imp_LF_Imp_bexp →
    mybool
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BTrue => mybool.mytrue
| _st, Original_LF__DOT__Imp_LF_Imp_bexp.BFalse => mybool.myfalse
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BEq a1 a2 =>
    nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNeq a1 a2 =>
    negb (nat_eqb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BLe a1 a2 =>
    nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BGt a1 a2 =>
    negb (nat_leb (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2))
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BNot b1 =>
    negb (Original_LF__DOT__Imp_LF_Imp_beval st b1)
| st, Original_LF__DOT__Imp_LF_Imp_bexp.BAnd b1 b2 =>
    andb (Original_LF__DOT__Imp_LF_Imp_beval st b1) (Original_LF__DOT__Imp_LF_Imp_beval st b2)

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- True type as Prop (exported as True)  
inductive TrueType : Prop
| I : TrueType

-- Alias for the checker
abbrev True' : Prop := TrueType
abbrev True'_I : TrueType := TrueType.I

-- bexp1: beval (X !-> 5) (true && ~(X <= 4)) = true
-- This is Admitted in Original.v, so we make it an axiom
axiom Original_LF__DOT__Imp_LF_Imp_bexp1 :
  @Corelib_Init_Logic_eq mybool
    (Original_LF__DOT__Imp_LF_Imp_beval
       (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X
          (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))
       (Original_LF__DOT__Imp_LF_Imp_bexp.BAnd Original_LF__DOT__Imp_LF_Imp_bexp.BTrue
          (Original_LF__DOT__Imp_LF_Imp_bexp.BNot
             (Original_LF__DOT__Imp_LF_Imp_bexp.BLe (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
                (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
    mybool.mytrue

-- eq for Prop (SProp in Rocq)
def Corelib_Init_Logic_eq_Prop (A : Prop) (a b : A) : Prop := TrueType
