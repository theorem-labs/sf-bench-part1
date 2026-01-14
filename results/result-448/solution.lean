-- Lean translation for reflect_involution and its dependencies
set_option autoImplicit false

-- True (using namespace to avoid collision)
namespace Exports
abbrev True : Prop := _root_.True
end Exports

-- Equality type (in Type)
inductive Corelib_Init_Logic_eq {α : Type} : α → α → Prop where
  | refl : (a : α) → Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {α : Type} (a : α) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- prod type from LF_DOT_Poly - but we'll use Prod directly for simplicity
def Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type := Prod X Y

-- Alias for pair constructor
def Original_LF__DOT__Poly_LF_Poly_pair {X Y : Type} (x : X) (y : Y) : Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Prod.mk x y

-- t_tree type - use a flat constructor to avoid nested recursion issues
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree (X : Type) : Type where
  | t_leaf : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X
  | t_branch : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X → X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X → Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X

-- reflect function
def Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect {X : Type} (t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X) : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X :=
  match t with
  | .t_leaf => .t_leaf
  | .t_branch l v r => .t_branch (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect r) v (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect l)

-- reflect_involution axiom (Admitted in Original.v)
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect__involution :
  ∀ (X : Type) (t : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_t__tree X),
    Corelib_Init_Logic_eq 
      (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect 
        (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_reflect t)) 
      t
