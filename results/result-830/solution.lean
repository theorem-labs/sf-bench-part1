-- Lean translation of Rocq Imp language definitions for s_compile_correct_aux

set_option linter.all false

-- Define our own bool type with names that won't conflict  
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Alias for Imported.bool, Imported.true, Imported.false
abbrev Imported_bool := mybool
abbrev Imported_true := mybool.mytrue
abbrev Imported_false := mybool.myfalse

-- Define our own nat type
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- Aliases that will become Imported.nat, etc.
def nat := mynat  
def nat_O := mynat.O
def nat_S := mynat.S

-- Nat operations
def nat_add : mynat → mynat → mynat
  | mynat.O, m => m
  | mynat.S n, m => mynat.S (nat_add n m)

def nat_sub : mynat → mynat → mynat
  | n, mynat.O => n
  | mynat.O, mynat.S _ => mynat.O
  | mynat.S n, mynat.S m => nat_sub n m

def nat_mul : mynat → mynat → mynat
  | mynat.O, _ => mynat.O
  | mynat.S n, m => nat_add m (nat_mul n m)

-- Define Ascii as 8 bools (like Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Ascii constructor alias
def Ascii_Ascii := Ascii_ascii.Ascii

-- String type (like Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- List type
inductive list (A : Type) : Type where
  | nil : list A
  | cons : A → list A → list A

-- Export constructors for list
def nil (A : Type) : list A := list.nil
def cons {A : Type} (h : A) (t : list A) : list A := list.cons h t

-- app function for list concatenation
def app (A : Type) : list A → list A → list A
  | list.nil, l2 => l2
  | list.cons h t, l2 => list.cons h (app A t l2)

-- Total map type (function from string to A)
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) := String_string → A

-- State is total_map nat
def Original_LF__DOT__Imp_LF_Imp_state := Original_LF__DOT__Maps_LF_Maps_total__map mynat

-- Arithmetic expressions (matches Original.LF_DOT_Imp.LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : mynat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- aexp constructor aliases
def Original_LF__DOT__Imp_LF_Imp_aexp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_aexp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_aexp_APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_aexp_AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- Stack instructions
inductive Original_LF__DOT__Imp_LF_Imp_sinstr : Type where
  | SPush : mynat → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SLoad : String_string → Original_LF__DOT__Imp_LF_Imp_sinstr
  | SPlus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMinus : Original_LF__DOT__Imp_LF_Imp_sinstr
  | SMult : Original_LF__DOT__Imp_LF_Imp_sinstr

-- sinstr constructor aliases
def Original_LF__DOT__Imp_LF_Imp_sinstr_SPush := Original_LF__DOT__Imp_LF_Imp_sinstr.SPush
def Original_LF__DOT__Imp_LF_Imp_sinstr_SLoad := Original_LF__DOT__Imp_LF_Imp_sinstr.SLoad
def Original_LF__DOT__Imp_LF_Imp_sinstr_SPlus := Original_LF__DOT__Imp_LF_Imp_sinstr.SPlus
def Original_LF__DOT__Imp_LF_Imp_sinstr_SMinus := Original_LF__DOT__Imp_LF_Imp_sinstr.SMinus
def Original_LF__DOT__Imp_LF_Imp_sinstr_SMult := Original_LF__DOT__Imp_LF_Imp_sinstr.SMult

-- True type as Prop (will be exported as SProp in Rocq)
inductive TrueType : Prop where
  | I : TrueType

def TrueType_I : TrueType := TrueType.I

-- False type as Prop
inductive FalseType : Prop where

-- Equality type in Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl

-- Equality for Prop-level elements (for use when A : Prop)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- aeval: evaluates arithmetic expression in a state
def Original_LF__DOT__Imp_LF_Imp_aeval (st : Original_LF__DOT__Imp_LF_Imp_state) : Original_LF__DOT__Imp_LF_Imp_aexp → mynat
  | Original_LF__DOT__Imp_LF_Imp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_aexp.AId x => st x
  | Original_LF__DOT__Imp_LF_Imp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)
  | Original_LF__DOT__Imp_LF_Imp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_aeval st a1) (Original_LF__DOT__Imp_LF_Imp_aeval st a2)

-- s_compile and s_execute are Admitted in Original.v, so we axiomatize them
axiom Original_LF__DOT__Imp_LF_Imp_s__compile : Original_LF__DOT__Imp_LF_Imp_aexp → list Original_LF__DOT__Imp_LF_Imp_sinstr

axiom Original_LF__DOT__Imp_LF_Imp_s__execute : 
  Original_LF__DOT__Imp_LF_Imp_state → list mynat → list Original_LF__DOT__Imp_LF_Imp_sinstr → list mynat

-- s_compile_correct_aux: the main theorem we're proving an isomorphism for
-- This is Admitted in Original.v
axiom Original_LF__DOT__Imp_LF_Imp_s__compile__correct__aux :
  ∀ (st : Original_LF__DOT__Imp_LF_Imp_state) (e : Original_LF__DOT__Imp_LF_Imp_aexp) (stack : list mynat),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Imp_LF_Imp_s__execute st stack (Original_LF__DOT__Imp_LF_Imp_s__compile e))
    (list.cons (Original_LF__DOT__Imp_LF_Imp_aeval st e) stack)
