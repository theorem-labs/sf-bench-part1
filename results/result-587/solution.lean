-- Use Lean's built-in True but give it an alias we can export
def myTrue := _root_.True

-- Equality in Prop (will become SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

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

-- List reverse function
def Original_LF__DOT__Poly_LF_Poly_rev (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_app X (Original_LF__DOT__Poly_LF_Poly_rev X t) 
        (Original_LF__DOT__Poly_LF_Poly_list.cons h Original_LF__DOT__Poly_LF_Poly_list.nil)

-- List map function
def Original_LF__DOT__Poly_LF_Poly_map (X Y : Type) (f : X → Y) : Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list Y
  | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
  | Original_LF__DOT__Poly_LF_Poly_list.cons h t => 
      Original_LF__DOT__Poly_LF_Poly_list.cons (f h) (Original_LF__DOT__Poly_LF_Poly_map X Y f t)

-- The map_rev axiom (it's Admitted in the original)
axiom Original_LF__DOT__Poly_LF_Poly_map__rev : ∀ (X Y : Type) (f : X → Y) (l : Original_LF__DOT__Poly_LF_Poly_list X),
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_map X Y f (Original_LF__DOT__Poly_LF_Poly_rev X l))
    (Original_LF__DOT__Poly_LF_Poly_rev Y (Original_LF__DOT__Poly_LF_Poly_map X Y f l))
