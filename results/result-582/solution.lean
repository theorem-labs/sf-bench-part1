-- Lean 4 translation of Rocq Imp language definitions

-- Define nat inductively (like Rocq's nat)
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- Nat operations
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (Nat_add n m)

def Nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, nat.S _ => nat.O
  | nat.S n, nat.S m => Nat_sub n m

def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => Nat_add m (Nat_mul n m)

def Nat_pred : nat → nat
  | nat.O => nat.O
  | nat.S n => n

-- Logic definitions
inductive myTrue : Prop where
  | I : myTrue

inductive myFalse : Prop where

-- Equality (matching Corelib.Init.Logic.eq)
inductive Corelib_Init_Logic_eq {A : Sort u} (a : A) : A → Prop where
  | eq_refl : Corelib_Init_Logic_eq a a

-- List type
inductive list (A : Type u) : Type u where
  | nil : list A
  | cons : A → list A → list A

-- Option type
inductive option (A : Type u) : Type u where
  | None : option A
  | Some : A → option A

-- Option constructors
def None := @option.None
def Some := @option.Some

-- Relation type
def Original_LF_Rel_relation (X : Type u) := X → X → Prop

-- Or (disjunction)
inductive myOr (A B : Prop) : Prop where
  | inl : A → myOr A B
  | inr : B → myOr A B

-- Not (negation)
def Logic_not (A : Prop) : Prop := A → myFalse

-- List membership (In) as a fixpoint
def List_In {A : Type u} (a : A) : list A → Prop
  | list.nil => myFalse
  | list.cons b l => myOr (Corelib_Init_Logic_eq b a) (List_In a l)

-- Define mybool (for Ascii and Datatypes.bool)
inductive mybool : Type where
  | mytrue : mybool
  | myfalse : mybool

-- Define ascii as 8 booleans (like Rocq's Ascii.ascii)
inductive Ascii_ascii : Type where
  | Ascii : mybool → mybool → mybool → mybool → mybool → mybool → mybool → mybool → Ascii_ascii

-- Constructor alias for Ascii.Ascii
def Ascii_Ascii := Ascii_ascii.Ascii

-- Define string using ascii (like Rocq's String.string)
inductive String_string : Type where
  | EmptyString : String_string
  | String : Ascii_ascii → String_string → String_string

-- Define aexp (LF.Imp.aexp)
inductive Original_LF__DOT__Imp_LF_Imp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aexp
  | AId : String_string → Original_LF__DOT__Imp_LF_Imp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp

-- Define bexp (LF.Imp.bexp)
inductive Original_LF__DOT__Imp_LF_Imp_bexp : Type where
  | BTrue : Original_LF__DOT__Imp_LF_Imp_bexp
  | BFalse : Original_LF__DOT__Imp_LF_Imp_bexp
  | BEq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNeq : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BLe : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BGt : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BNot : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp
  | BAnd : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_bexp

-- Define com (LF.Imp.com)
inductive Original_LF__DOT__Imp_LF_Imp_com : Type where
  | CSkip : Original_LF__DOT__Imp_LF_Imp_com
  | CAsgn : String_string → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_com
  | CSeq : Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CIf : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com
  | CWhile : Original_LF__DOT__Imp_LF_Imp_bexp → Original_LF__DOT__Imp_LF_Imp_com → Original_LF__DOT__Imp_LF_Imp_com

-- Export constructors
def ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def APlus := Original_LF__DOT__Imp_LF_Imp_aexp.APlus
def AMinus := Original_LF__DOT__Imp_LF_Imp_aexp.AMinus
def AMult := Original_LF__DOT__Imp_LF_Imp_aexp.AMult

def CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn

-- Full name constructors for checker compatibility
def Original_LF__DOT__Imp_LF_Imp_ANum := Original_LF__DOT__Imp_LF_Imp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AId := Original_LF__DOT__Imp_LF_Imp_aexp.AId
def Original_LF__DOT__Imp_LF_Imp_CAsgn := Original_LF__DOT__Imp_LF_Imp_com.CAsgn

-- Define Original_LF__DOT__Imp_LF_Imp_APlus for APlus constructor iso
def Original_LF__DOT__Imp_LF_Imp_APlus : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp :=
  Original_LF__DOT__Imp_LF_Imp_aexp.APlus

-- Variable X = "X" in string form
-- X = String (Ascii true false false false true false true false) EmptyString
-- ASCII for 'X' is 88 = 01011000 in binary = false false false true true false true false (little-endian bits)
-- Actually Ascii.ascii in Rocq is (b0 b1 b2 b3 b4 b5 b6 b7) where bn is bit n
-- 'X' = 88 = 0x58 = 01011000
-- bit 0 = 0, bit 1 = 0, bit 2 = 0, bit 3 = 1, bit 4 = 1, bit 5 = 0, bit 6 = 1, bit 7 = 0
def Original_LF__DOT__Imp_LF_Imp_X : String_string :=
  String_string.String
    (Ascii_ascii.Ascii mybool.myfalse mybool.myfalse mybool.myfalse mybool.mytrue
                       mybool.mytrue mybool.myfalse mybool.mytrue mybool.myfalse)
    String_string.EmptyString

-- plus2 : com = X := X + 2
-- = CAsgn X (APlus (AId X) (ANum 2))
-- 2 = S (S O)
def Original_LF__DOT__Imp_LF_Imp_plus2 : Original_LF__DOT__Imp_LF_Imp_com :=
  Original_LF__DOT__Imp_LF_Imp_com.CAsgn
    Original_LF__DOT__Imp_LF_Imp_X
    (Original_LF__DOT__Imp_LF_Imp_aexp.APlus
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S nat.O))))

-- Define AMult constructor for export
def Original_LF__DOT__Imp_LF_Imp_AMult : Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp → Original_LF__DOT__Imp_LF_Imp_aexp :=
  Original_LF__DOT__Imp_LF_Imp_aexp.AMult

-- example_aexp = APlus (ANum 3) (AMult (AId X) (ANum 2))
-- 3 = S (S (S O))
-- 2 = S (S O)
def Original_LF__DOT__Imp_LF_Imp_example__aexp : Original_LF__DOT__Imp_LF_Imp_aexp :=
  Original_LF__DOT__Imp_LF_Imp_aexp.APlus
    (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S (nat.S nat.O))))
    (Original_LF__DOT__Imp_LF_Imp_aexp.AMult
      (Original_LF__DOT__Imp_LF_Imp_aexp.AId Original_LF__DOT__Imp_LF_Imp_X)
      (Original_LF__DOT__Imp_LF_Imp_aexp.ANum (nat.S (nat.S nat.O))))
