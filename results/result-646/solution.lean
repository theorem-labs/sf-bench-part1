-- Lean translation for no_whiles_eqv and all dependencies

-- Custom bool to avoid Lean stdlib issues  
inductive mybool : Type where
  | true : mybool
  | false : mybool

-- Custom nat
inductive mynat : Type where
  | O : mynat
  | S : mynat → mynat

-- Custom ascii (8 bools)
inductive myascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → myascii

-- Custom string
inductive String_string : Type where
  | EmptyString : String_string
  | String : myascii → String_string → String_string

-- aexp: arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : mynat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- bexp: boolean expressions
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- com: commands
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- andb for boolean and
def mybool_andb : mybool → mybool → mybool
  | .true, b => b
  | .false, _ => .false

-- no_whiles: checks if a command contains no while loops
def Original_LF__DOT__Imp_LF_Imp_no__whiles : Original_LF__DOT__Imp_LF_Imp_com → mybool
  | .CSkip => .true
  | .CAsgn _ _ => .true
  | .CSeq c1 c2 => mybool_andb (Original_LF__DOT__Imp_LF_Imp_no__whiles c1) (Original_LF__DOT__Imp_LF_Imp_no__whiles c2)
  | .CIf _ ct cf => mybool_andb (Original_LF__DOT__Imp_LF_Imp_no__whiles ct) (Original_LF__DOT__Imp_LF_Imp_no__whiles cf)
  | .CWhile _ _ => .false

-- no_whilesR: inductive predicate (empty - no constructors)
inductive Original_LF__DOT__Imp_LF_Imp_no__whilesR : Original_LF__DOT__Imp_LF_Imp_com → Prop where

-- True in Prop (becomes SProp when imported)
inductive PTrue : Prop where
  | intro : PTrue



-- Equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (also becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- iff as a structure so it becomes a record with primitive projections
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- The no_whiles_eqv axiom: This is Admitted in Original.v
axiom Original_LF__DOT__Imp_LF_Imp_no__whiles__eqv : ∀ (x : Original_LF__DOT__Imp_LF_Imp_com),
  iff (Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_no__whiles x) mybool.true) (Original_LF__DOT__Imp_LF_Imp_no__whilesR x)
