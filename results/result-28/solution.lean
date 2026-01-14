-- Lean translation of Original.LF_DOT_IndPrinciples.LF.IndPrinciples.tree

inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree (X : Type) : Type where
  | leaf : X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree X
  | node : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_tree X
