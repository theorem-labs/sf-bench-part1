-- Translation of comparison, letter, letter_comparison, lower_letter, and lower_letter_F_is_F from Rocq

-- For True - avoid conflict with Lean's True by using a different identifier
-- We'll edit the .out file to rename this to True after export
inductive MyTrue : Prop where
  | intro : MyTrue

-- For eq (Type equality)
def Corelib_Init_Logic_eq {A : Type} (a b : A) : Prop := a = b

-- For eq (Prop equality) - when A is Prop
def Corelib_Init_Logic_eq_Prop {A : Prop} (a b : A) : Prop := a = b

-- Inductive comparison : Type := Eq | Lt | Gt.
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Eq

def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Lt

def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- Inductive letter : Type := A | B | C | D | F.
inductive Original_LF__DOT__Basics_LF_Basics_letter : Type where
  | A : Original_LF__DOT__Basics_LF_Basics_letter
  | B : Original_LF__DOT__Basics_LF_Basics_letter
  | C : Original_LF__DOT__Basics_LF_Basics_letter
  | D : Original_LF__DOT__Basics_LF_Basics_letter
  | F : Original_LF__DOT__Basics_LF_Basics_letter

def Original_LF__DOT__Basics_LF_Basics_A : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.A

def Original_LF__DOT__Basics_LF_Basics_B : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.B

def Original_LF__DOT__Basics_LF_Basics_C : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.C

def Original_LF__DOT__Basics_LF_Basics_D : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.D

def Original_LF__DOT__Basics_LF_Basics_F : Original_LF__DOT__Basics_LF_Basics_letter := 
  Original_LF__DOT__Basics_LF_Basics_letter.F

-- Definition letter_comparison (l1 l2 : letter) : comparison
def Original_LF__DOT__Basics_LF_Basics_letter__comparison 
    (l1 l2 : Original_LF__DOT__Basics_LF_Basics_letter) : Original_LF__DOT__Basics_LF_Basics_comparison :=
  match l1, l2 with
  | .A, .A => .Eq
  | .A, _ => .Gt
  | .B, .A => .Lt
  | .B, .B => .Eq
  | .B, _ => .Gt
  | .C, .A => .Lt
  | .C, .B => .Lt
  | .C, .C => .Eq
  | .C, _ => .Gt
  | .D, .A => .Lt
  | .D, .B => .Lt
  | .D, .C => .Lt
  | .D, .D => .Eq
  | .D, _ => .Gt
  | .F, .A => .Lt
  | .F, .B => .Lt
  | .F, .C => .Lt
  | .F, .D => .Lt
  | .F, .F => .Eq

-- Definition lower_letter (l : letter) : letter
def Original_LF__DOT__Basics_LF_Basics_lower__letter 
    (l : Original_LF__DOT__Basics_LF_Basics_letter) : Original_LF__DOT__Basics_LF_Basics_letter :=
  match l with
  | .A => .B
  | .B => .C
  | .C => .D
  | .D => .F
  | .F => .F

-- Theorem lower_letter_F_is_F (Admitted in original)
-- lower_letter F = F
axiom Original_LF__DOT__Basics_LF_Basics_lower__letter__F__is__F :
  Corelib_Init_Logic_eq (Original_LF__DOT__Basics_LF_Basics_lower__letter Original_LF__DOT__Basics_LF_Basics_F) Original_LF__DOT__Basics_LF_Basics_F
