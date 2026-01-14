-- Lean translation of Rocq Imp language definitions for s_execute1

-- Boolean type (for internal use)
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
def nil (A : Type) : list A := list.nil
def cons (A : Type) : A → list A → list A := list.cons

-- Total map type
def Original_LF__DOT__Maps_LF_Maps_total__map (A : Type) : Type := String_string → A

-- t_empty for total_map
def Original_LF__DOT__Maps_LF_Maps_t__empty (A : Type) (v : A) : Original_LF__DOT__Maps_LF_Maps_total__map A :=
  fun _ => v

-- State type
def Original_LF__DOT__Imp_LF_Imp_state : Type := Original_LF__DOT__Maps_LF_Maps_total__map nat

-- empty_st: state that maps everything to 0
def Original_LF__DOT__Imp_LF_Imp_empty__st : String_string → nat :=
  fun _ => nat.O

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

-- True type as Prop (will be exported as SProp in Rocq)
inductive TrueType : Prop
| I : TrueType

def TrueType_I : TrueType := TrueType.I

-- Equality type in Prop (will become SProp in Rocq) - for Type-level equality
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq a a

-- Equality type in Prop for Prop-level equality (needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop
| refl : Corelib_Init_Logic_eq_Prop a a

-- Axiomatized s_execute function (since it's Admitted in Original.v)
axiom Original_LF__DOT__Imp_LF_Imp_s__execute :
  Original_LF__DOT__Imp_LF_Imp_state → list nat → list Original_LF__DOT__Imp_LF_Imp_sinstr → list nat

-- s_execute1 axiom: s_execute empty_st [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5]
axiom Original_LF__DOT__Imp_LF_Imp_s__execute1 :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Imp_LF_Imp_s__execute
       Original_LF__DOT__Imp_LF_Imp_empty__st
       (list.nil)
       (list.cons
          (Original_LF__DOT__Imp_LF_Imp_sinstr.SPush (nat.S (nat.S (nat.S (nat.S (nat.S nat.O))))))  -- 5
          (list.cons
             (Original_LF__DOT__Imp_LF_Imp_sinstr.SPush (nat.S (nat.S (nat.S nat.O))))  -- 3
             (list.cons
                (Original_LF__DOT__Imp_LF_Imp_sinstr.SPush (nat.S nat.O))  -- 1
                (list.cons
                   Original_LF__DOT__Imp_LF_Imp_sinstr.SMinus
                   list.nil)))))
    (list.cons
       (nat.S (nat.S nat.O))  -- 2
       (list.cons
          (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))  -- 5
          list.nil))
