-- Import list definition
import U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso

-- Definition of foo' that matches Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo'
-- Inductive foo' (X:Type) : Type :=
--   | C1 (l : list X) (f : foo' X)
--   | C2.
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' (X : Type) : Type where
  | C1 : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' X
  | C2 : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' X
