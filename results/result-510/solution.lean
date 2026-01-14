-- Lean translation of Rocq Imp language definitions for s_execute2

-- Boolean type
inductive mybool : Type
| mytrue : mybool
| myfalse : mybool

-- Ascii type
inductive Ascii_ascii : Type
| Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- String type
inductive String_string : Type
| EmptyString : String_string
| String : Ascii_ascii → String_string → String_string

-- Natural numbers
inductive nat : Type
| O : nat
| S : nat → nat

-- Aliases for constructors
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- List type
inductive list (A : Type) : Type
| nil : list A
| cons : A → list A → list A

-- Export constructors for list
def list_nil (A : Type) : list A := list.nil
def list_cons (A : Type) : A → list A → list A := list.cons

-- Aliases for Coq list names
def nil (A : Type) : list A := list.nil
def cons {A : Type} (h : A) (t : list A) : list A := list.cons h t

-- Total map type
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- Stack instructions
inductive Original_LF__DOT__Imp_LF_Imp_sinstr : Type
| SPush : nat → Original_LF__DOT__Imp_LF_Imp_sinstr
| SLoad : String_string → Original_LF__DOT__Imp_LF_Imp_sinstr
| SPlus : Original_LF__DOT__Imp_LF_Imp_sinstr
| SMinus : Original_LF__DOT__Imp_LF_Imp_sinstr
| SMult : Original_LF__DOT__Imp_LF_Imp_sinstr

-- Export sinstr constructors
def Original_LF__DOT__Imp_LF_Imp_SPush : nat → Original_LF__DOT__Imp_LF_Imp_sinstr := Original_LF__DOT__Imp_LF_Imp_sinstr.SPush
def Original_LF__DOT__Imp_LF_Imp_SLoad : String_string → Original_LF__DOT__Imp_LF_Imp_sinstr := Original_LF__DOT__Imp_LF_Imp_sinstr.SLoad
def Original_LF__DOT__Imp_LF_Imp_SPlus : Original_LF__DOT__Imp_LF_Imp_sinstr := Original_LF__DOT__Imp_LF_Imp_sinstr.SPlus
def Original_LF__DOT__Imp_LF_Imp_SMinus : Original_LF__DOT__Imp_LF_Imp_sinstr := Original_LF__DOT__Imp_LF_Imp_sinstr.SMinus
def Original_LF__DOT__Imp_LF_Imp_SMult : Original_LF__DOT__Imp_LF_Imp_sinstr := Original_LF__DOT__Imp_LF_Imp_sinstr.SMult

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
-- So we need: false, false, false, true, true, false, true, false (least significant bit first in Coq)
-- Actually in Coq's Ascii, the bit order is b0 b1 b2 b3 b4 b5 b6 b7 where b0 is LSB
-- 88 = 64 + 16 + 8 = 2^6 + 2^4 + 2^3
-- So bits: b0=0, b1=0, b2=0, b3=1, b4=1, b5=0, b6=1, b7=0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- True type as Prop (will be exported as SProp in Rocq)
inductive TrueType : Prop
| I : TrueType

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- Axiomatized s_execute function (since it's Admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_s__execute :
  Original_LF__DOT__Imp_LF_Imp_state → list nat → list Original_LF__DOT__Imp_LF_Imp_sinstr → list nat

-- The s_execute2 example as an axiom (since it's Admitted in Original.v)
-- s_execute2 states:
--   s_execute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15; 4]
axiom Original_LF__DOT__Imp_LF_Imp_s__execute2 :
  @Corelib_Init_Logic_eq (list nat)
    (Original_LF__DOT__Imp_LF_Imp_s__execute
       (Original_LF__DOT__Maps_LF_Maps_t__update Original_LF__DOT__Imp_LF_Imp_empty__st Original_LF__DOT__Imp_LF_Imp_X (nat.S (nat.S (nat.S nat.O))))
       (list.cons (nat.S (nat.S (nat.S nat.O))) (list.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) list.nil))
       (list.cons (Original_LF__DOT__Imp_LF_Imp_sinstr.SPush (nat.S (nat.S (nat.S (nat.S nat.O)))))
          (list.cons (Original_LF__DOT__Imp_LF_Imp_sinstr.SLoad Original_LF__DOT__Imp_LF_Imp_X)
             (list.cons Original_LF__DOT__Imp_LF_Imp_sinstr.SMult
                (list.cons Original_LF__DOT__Imp_LF_Imp_sinstr.SPlus list.nil)))))
    (list.cons (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))))))))
       (list.cons (nat.S (nat.S (nat.S (nat.S nat.O)))) list.nil))
