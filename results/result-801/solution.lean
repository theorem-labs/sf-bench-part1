-- Lean translation of Rocq Imp language definitions

-- Basic types
def string := String

-- Variables
def X : string := "X"
def Y : string := "Y" 
def Z : string := "Z"

-- Arithmetic expressions
inductive aexp : Type where
  | ANum : Nat → aexp
  | AId : string → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp

-- Boolean expressions
inductive bexp : Type where
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp → aexp → bexp
  | BNeq : aexp → aexp → bexp
  | BLe : aexp → aexp → bexp
  | BGt : aexp → aexp → bexp
  | BNot : bexp → bexp
  | BAnd : bexp → bexp → bexp

-- Commands
inductive com : Type where
  | CSkip : com
  | CAsgn : string → aexp → com
  | CSeq : com → com → com
  | CIf : bexp → com → com → com
  | CWhile : bexp → com → com

-- Export the constructors
export aexp (ANum AId APlus AMinus AMult)
export bexp (BTrue BFalse BEq BNeq BLe BGt BNot BAnd)
export com (CSkip CAsgn CSeq CIf CWhile)

-- The factorial program
def fact_in_coq : com :=
  CSeq (CAsgn Z (AId X))
    (CSeq (CAsgn Y (ANum 1))
      (CWhile (BNeq (AId Z) (ANum 0))
        (CSeq (CAsgn Y (AMult (AId Y) (AId Z)))
          (CAsgn Z (AMinus (AId Z) (ANum 1))))))