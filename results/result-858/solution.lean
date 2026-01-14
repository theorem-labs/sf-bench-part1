-- Lean translation for s_compile1 isomorphism
-- s_compile1: s_compile <{ X - (2 * Y) }> = [SLoad X; SPush 2; SLoad Y; SMult; SMinus]

set_option linter.all false

-- ============================================================
-- Basic Types
-- ============================================================

-- bool type (matching Coq's bool)
inductive Coq_bool : Type where
  | Coq_true : Coq_bool
  | Coq_false : Coq_bool

-- mybool as a separate inductive for the String isomorphism file
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

def mybool_mytrue := mybool.mytrue
def mybool_myfalse := mybool.myfalse

-- Bool operations
def Bool_eqb : mybool → mybool → mybool
  | mybool.mytrue, mybool.mytrue => mybool.mytrue
  | mybool.myfalse, mybool.myfalse => mybool.mytrue
  | _, _ => mybool.myfalse

def andb : mybool → mybool → mybool
  | mybool.mytrue, b => b
  | mybool.myfalse, _ => mybool.myfalse

-- Custom nat
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S
def nat_O : nat := nat.O
def nat_S : nat → nat := nat.S

-- Alias for bool (mybool is already defined above)
-- The export will be manually edited to rename mybool_alias to bool
def mybool_alias := mybool
def mybool_alias_true := mybool.mytrue
def mybool_alias_false := mybool.myfalse

-- Nat operations
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

-- ============================================================
-- List
-- ============================================================

inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

def nil (A : Type) : list A := list.nil
def cons (A : Type) (h : A) (t : list A) : list A := list.cons h t
def list_nil (A : Type) : list A := list.nil
def list_cons (A : Type) (h : A) (t : list A) : list A := list.cons h t

def app (A : Type) : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => list.cons h (app A t l2)

-- ============================================================
-- Ascii and String
-- ============================================================

-- Custom ascii (8 bools)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

def Ascii_Ascii := Ascii_ascii.Ascii
def Ascii_ascii_Ascii := Ascii_ascii.Ascii

-- Alias for Ascii
def Ascii := Ascii_ascii

-- Ascii equality
def Ascii_eqb : Ascii_ascii → Ascii_ascii → mybool
  | Ascii_ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7, Ascii_ascii.Ascii c0 c1 c2 c3 c4 c5 c6 c7 =>
    andb (Bool_eqb b0 c0)
      (andb (Bool_eqb b1 c1)
        (andb (Bool_eqb b2 c2)
          (andb (Bool_eqb b3 c3)
            (andb (Bool_eqb b4 c4)
              (andb (Bool_eqb b5 c5)
                (andb (Bool_eqb b6 c6)
                  (Bool_eqb b7 c7)))))))

-- Custom string
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

def String_EmptyString := String_string.EmptyString
def String_String := String_string.String
def String_string_EmptyString := String_string.EmptyString
def String_string_String := String_string.String

-- String equality
def String_eqb : String_string → String_string → mybool
  | String_string.EmptyString, String_string.EmptyString => mybool.mytrue
  | String_string.String c1 s1, String_string.String c2 s2 =>
    andb (Ascii_eqb c1 c2) (String_eqb s1 s2)
  | _, _ => mybool.myfalse

-- ============================================================
-- Prop-level types
-- ============================================================

-- Equality in Prop (for Type arguments)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl (A : Type) (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality in Prop (for Prop arguments)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl (A : Prop) (a : A) : Corelib_Init_Logic_eq_Prop a a :=
  Corelib_Init_Logic_eq_Prop.refl a

-- Induction principle for Corelib_Init_Logic_eq_Prop (left version)
-- Need to type this differently to avoid sorries
axiom Corelib_Init_Logic_eq_Prop_indl : (A : Prop) → (x : A) → (P : A → Prop) → 
  P x → (y : A) → Corelib_Init_Logic_eq_Prop x y → P y

-- TrueType (maps to Coq's True)
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I : TrueType := TrueType.I

-- Alias for True export - these will be manually fixed in .out file
-- def «True» := TrueType  -- conflicts with Lean's True
def True_I := TrueType.I

-- FalseType (maps to Coq's False)
inductive FalseType : Prop where

-- Alias for False (will be renamed in export)
def FalseType_alias := FalseType

-- List_In: membership predicate for lists
def List_In (A : Type) (a : A) : list A → Prop
  | list.nil => FalseType
  | list.cons x xs => Corelib_Init_Logic_eq x a ∨ List_In A a xs

-- Logic_not: negation
def Logic_not (P : Prop) : Prop := P → FalseType

-- and (conjunction)
inductive and_type (A B : Prop) : Prop where
  | conj : A → B → and_type A B

def «and» := and_type

-- or (disjunction)
inductive or_type (A B : Prop) : Prop where
  | or_introl : A → or_type A B
  | or_intror : B → or_type A B

def «or» := or_type

-- iff (if and only if)
def iff (A B : Prop) : Prop := and_type (A → B) (B → A)

-- ex (existential)
inductive ex_type (A : Type) (P : A → Prop) : Prop where
  | ex_intro : (x : A) → P x → ex_type A P

def «ex» := ex_type

-- option type
inductive option (A : Type) : Type where
  | None : option A
  | Some : A → option A

def None (A : Type) : option A := option.None
def Some (A : Type) (a : A) : option A := option.Some a

-- prod type  
inductive prod (A B : Type) : Type where
  | pair : A → B → prod A B

def pair (A B : Type) (a : A) (b : B) : prod A B := prod.pair a b

-- unit type
inductive unit_type : Type where
  | tt : unit_type

def «unit» := unit_type

def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Comparison
def le (n m : nat) : Prop := ∃ k, Nat_add n k = m
def lt (n m : nat) : Prop := le (nat.S n) m
def ge (n m : nat) : Prop := le m n
def gt (n m : nat) : Prop := lt m n

-- ============================================================
-- Maps
-- ============================================================

-- total_map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- t_update function
def Original_LF__DOT__Maps_LF_Maps_t__update {A : Type} (m : Original_LF__DOT__Maps_LF_Maps_total__map A)
    (x : String_string) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun x' => match String_eqb x x' with
    | mybool.mytrue => v
    | mybool.myfalse => m x'

-- t_empty function
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- ============================================================
-- Imp Language Types
-- ============================================================

-- State is total_map nat
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- X variable: 'X' in ASCII is 88 = 01011000
-- Bits: b0=0, b1=0, b2=0, b3=1, b4=1, b5=0, b6=1, b7=0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- Y variable: 'Y' in ASCII is 89 = 01011001
-- Bits: b0=1, b1=0, b2=0, b3=1, b4=1, b5=0, b6=1, b7=0
def Original_LF__DOT__Imp_LF_Imp_Y : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.mytrue mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- aexp constructor aliases
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Stack instructions
inductive Original_LF__DOT__Imp_LF_Imp_sinstr : Type where
  | SPush : nat → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SLoad : String_string → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SPlus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMinus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMult : Original_LF__DOT__Imp_LF_Imp_sinstr

-- sinstr constructor aliases
def Original_LF__DOT__Imp_LF_Imp_SPush := Original_LF__DOT__Imp_LF_Imp_sinstr.SPush
def Original_LF__DOT__Imp_LF_Imp_SLoad := Original_LF__DOT__Imp_LF_Imp_sinstr.SLoad
def Original_LF__DOT__Imp_LF_Imp_SPlus := Original_LF__DOT__Imp_LF_Imp_sinstr.SPlus
def Original_LF__DOT__Imp_LF_Imp_SMinus := Original_LF__DOT__Imp_LF_Imp_sinstr.SMinus
def Original_LF__DOT__Imp_LF_Imp_SMult := Original_LF__DOT__Imp_LF_Imp_sinstr.SMult

-- ============================================================
-- s_compile (axiomatized since it's Admitted in Original.v)
-- ============================================================

axiom Original_LF__DOT__Imp_LF_Imp_s__compile : Original_LF__DOT__Imp_LF_Imp_aexp → list Original_LF__DOT__Imp_LF_Imp_sinstr

-- ============================================================
-- s_compile1: the theorem we need to prove isomorphism for
-- s_compile <{ X - (2 * Y) }> = [SLoad X; SPush 2; SLoad Y; SMult; SMinus]
-- ============================================================

-- The s_compile1 theorem (axiomatized since it's Admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_s__compile1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_s__compile 
      (Original_LF__DOT__Imp_LF_Imp_AMinus
        (Original_LF__DOT__Imp_LF_Imp_AId Original_LF__DOT__Imp_LF_Imp_X)
        (Original_LF__DOT__Imp_LF_Imp_AMult
          (Original_LF__DOT__Imp_LF_Imp_ANum (S (S _0)))
          (Original_LF__DOT__Imp_LF_Imp_AId Original_LF__DOT__Imp_LF_Imp_Y))))
    (cons Original_LF__DOT__Imp_LF_Imp_sinstr (Original_LF__DOT__Imp_LF_Imp_SLoad Original_LF__DOT__Imp_LF_Imp_X)
      (cons Original_LF__DOT__Imp_LF_Imp_sinstr (Original_LF__DOT__Imp_LF_Imp_SPush (S (S _0)))
        (cons Original_LF__DOT__Imp_LF_Imp_sinstr (Original_LF__DOT__Imp_LF_Imp_SLoad Original_LF__DOT__Imp_LF_Imp_Y)
          (cons Original_LF__DOT__Imp_LF_Imp_sinstr Original_LF__DOT__Imp_LF_Imp_SMult
            (cons Original_LF__DOT__Imp_LF_Imp_sinstr Original_LF__DOT__Imp_LF_Imp_SMinus (nil Original_LF__DOT__Imp_LF_Imp_sinstr))))))
