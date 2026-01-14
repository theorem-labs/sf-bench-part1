-- Lean translation of Rocq definitions for LF.Basics

-- Bool type
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- RGB type
inductive Original_LF__DOT__Basics_LF_Basics_rgb : Type where
  | red : Original_LF__DOT__Basics_LF_Basics_rgb
  | green : Original_LF__DOT__Basics_LF_Basics_rgb
  | blue : Original_LF__DOT__Basics_LF_Basics_rgb

-- Color type
inductive Original_LF__DOT__Basics_LF_Basics_color : Type where
  | black : Original_LF__DOT__Basics_LF_Basics_color
  | white : Original_LF__DOT__Basics_LF_Basics_color
  | primary : Original_LF__DOT__Basics_LF_Basics_rgb → Original_LF__DOT__Basics_LF_Basics_color

-- true and false constants
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool := 
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool := 
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- isred function
def Original_LF__DOT__Basics_LF_Basics_isred (c : Original_LF__DOT__Basics_LF_Basics_color) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match c with
  | Original_LF__DOT__Basics_LF_Basics_color.black => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_color.white => Original_LF__DOT__Basics_LF_Basics_bool.false
  | Original_LF__DOT__Basics_LF_Basics_color.primary Original_LF__DOT__Basics_LF_Basics_rgb.red => Original_LF__DOT__Basics_LF_Basics_bool.true
  | Original_LF__DOT__Basics_LF_Basics_color.primary _ => Original_LF__DOT__Basics_LF_Basics_bool.false

-- Playground.foo : rgb := blue
def Original_LF__DOT__Basics_LF_Basics_Playground_foo : Original_LF__DOT__Basics_LF_Basics_rgb :=
  Original_LF__DOT__Basics_LF_Basics_rgb.blue
