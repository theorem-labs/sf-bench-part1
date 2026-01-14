-- Lean 4 translation of Rocq definitions

-- Bool type (from LF.Basics)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

-- Explicit definitions for true and false
def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool := Original_LF__DOT__Basics_LF_Basics_bool.true
def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool := Original_LF__DOT__Basics_LF_Basics_bool.false

-- bit type: represents a single bit (B1 or B0)
inductive Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit : Type where
  | B1 : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit
  | B0 : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit

-- nybble type: represents 4 bits
inductive Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble : Type where
  | bits : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit → 
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit → 
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit → 
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit → 
           Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble

-- all_zero function: checks if all bits in a nybble are B0
def Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero 
    (nb : Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match nb with
  | Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble.bits 
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0
      Original_LF__DOT__Basics_LF_Basics_TuplePlayground_bit.B0 => Original_LF__DOT__Basics_LF_Basics_bool.true
  | _ => Original_LF__DOT__Basics_LF_Basics_bool.false
