-- Translation of Original.LF_DOT_Basics.LF.Basics.bw and invert

-- bw type with two constructors
inductive Original_LF__DOT__Basics_LF_Basics_bw : Type where
  | bw_black : Original_LF__DOT__Basics_LF_Basics_bw
  | bw_white : Original_LF__DOT__Basics_LF_Basics_bw

-- invert function: swaps black and white
-- In Rocq: if x then bw_white else bw_black
-- which means: bw_black -> bw_white, bw_white -> bw_black
def Original_LF__DOT__Basics_LF_Basics_invert (x : Original_LF__DOT__Basics_LF_Basics_bw) : Original_LF__DOT__Basics_LF_Basics_bw :=
  match x with
  | Original_LF__DOT__Basics_LF_Basics_bw.bw_black => Original_LF__DOT__Basics_LF_Basics_bw.bw_white
  | Original_LF__DOT__Basics_LF_Basics_bw.bw_white => Original_LF__DOT__Basics_LF_Basics_bw.bw_black
