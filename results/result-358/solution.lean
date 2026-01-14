-- Lean translation of Rocq definitions from Original.v

-- comparison type
inductive Original_LF__DOT__Basics_LF_Basics_comparison : Type where
  | Eq : Original_LF__DOT__Basics_LF_Basics_comparison
  | Lt : Original_LF__DOT__Basics_LF_Basics_comparison
  | Gt : Original_LF__DOT__Basics_LF_Basics_comparison

-- Constructor aliases
def Original_LF__DOT__Basics_LF_Basics_Eq : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Eq

def Original_LF__DOT__Basics_LF_Basics_Lt : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Lt

def Original_LF__DOT__Basics_LF_Basics_Gt : Original_LF__DOT__Basics_LF_Basics_comparison := 
  Original_LF__DOT__Basics_LF_Basics_comparison.Gt

-- modifier type
inductive Original_LF__DOT__Basics_LF_Basics_modifier : Type where
  | Plus : Original_LF__DOT__Basics_LF_Basics_modifier
  | Natural : Original_LF__DOT__Basics_LF_Basics_modifier
  | Minus : Original_LF__DOT__Basics_LF_Basics_modifier

-- Constructor aliases
def Original_LF__DOT__Basics_LF_Basics_Plus : Original_LF__DOT__Basics_LF_Basics_modifier := 
  Original_LF__DOT__Basics_LF_Basics_modifier.Plus

def Original_LF__DOT__Basics_LF_Basics_Natural : Original_LF__DOT__Basics_LF_Basics_modifier := 
  Original_LF__DOT__Basics_LF_Basics_modifier.Natural

def Original_LF__DOT__Basics_LF_Basics_Minus : Original_LF__DOT__Basics_LF_Basics_modifier := 
  Original_LF__DOT__Basics_LF_Basics_modifier.Minus

-- modifier_comparison function
def Original_LF__DOT__Basics_LF_Basics_modifier__comparison 
  (m1 m2 : Original_LF__DOT__Basics_LF_Basics_modifier) : Original_LF__DOT__Basics_LF_Basics_comparison :=
  match m1, m2 with
  | .Plus, .Plus => .Eq
  | .Plus, _ => .Gt
  | .Natural, .Plus => .Lt
  | .Natural, .Natural => .Eq
  | .Natural, _ => .Gt
  | .Minus, .Plus => .Lt
  | .Minus, .Natural => .Lt
  | .Minus, .Minus => .Eq
