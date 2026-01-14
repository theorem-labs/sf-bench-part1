-- Equality in Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (specialized version)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Use Lean's built-in True but give it an alias we can export
def myTrue := _root_.True

-- Polymorphic list type
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- List constructors
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons

-- List append function
def Original_LF__DOT__Poly_LF_Poly_app (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil, l2 => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t, l2 => Original_LF__DOT__Poly_LF_Poly_list.cons h (Original_LF__DOT__Poly_LF_Poly_app X t l2)

-- Reverse function (standard, using app)
def Original_LF__DOT__Poly_LF_Poly_rev (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_rev X t) (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- Tail-recursive reverse helper
def Original_LF__DOT__Logic_LF_Logic_rev__append (X : Type) (l1 l2 : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  match l1 with
  | Original_LF__DOT__Poly_LF_Poly_list.nil => l2
  | Original_LF__DOT__Poly_LF_Poly_list.cons x l1' => 
      Original_LF__DOT__Logic_LF_Logic_rev__append X l1' (Original_LF__DOT__Poly_LF_Poly_list.cons x l2)

-- Tail-recursive reverse
def Original_LF__DOT__Logic_LF_Logic_tr__rev (X : Type) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Logic_LF_Logic_rev__append X l Original_LF__DOT__Poly_LF_Poly_list.nil

-- The correctness theorem (Admitted in Original, so we use axiom)
axiom Original_LF__DOT__Logic_LF_Logic_tr__rev__correct : ∀ (X : Type),
  @Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X)
    (fun l => Original_LF__DOT__Logic_LF_Logic_tr__rev X l)
    (fun l => Original_LF__DOT__Poly_LF_Poly_rev X l)
