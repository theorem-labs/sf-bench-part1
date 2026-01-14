-- Definitions for list, prod, pair, nil, cons, combine, split, and combine_split

-- Custom equality type (to avoid SProp issues)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Type where
  | refl : (a : A) → Corelib_Init_Logic_eq a a

-- True type - use Lean's built-in Unit as it maps to Rocq's True
-- Unit has one constructor: Unit.unit

-- List type (matching Original.LF_DOT_Poly.LF.Poly.list)
inductive Original_LF__DOT__Poly_LF_Poly_list (X : Type) : Type where
  | nil : Original_LF__DOT__Poly_LF_Poly_list X
  | cons : X → Original_LF__DOT__Poly_LF_Poly_list X → Original_LF__DOT__Poly_LF_Poly_list X

-- The nil constructor
def Original_LF__DOT__Poly_LF_Poly_nil (X : Type) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.nil

-- The cons constructor  
def Original_LF__DOT__Poly_LF_Poly_cons (X : Type) (x : X) (l : Original_LF__DOT__Poly_LF_Poly_list X) : Original_LF__DOT__Poly_LF_Poly_list X :=
  Original_LF__DOT__Poly_LF_Poly_list.cons x l

-- Prod type (matching Original.LF_DOT_Poly.LF.Poly.prod)
inductive Original_LF__DOT__Poly_LF_Poly_prod (X Y : Type) : Type where
  | pair : X → Y → Original_LF__DOT__Poly_LF_Poly_prod X Y

-- The pair constructor
def Original_LF__DOT__Poly_LF_Poly_pair (X Y : Type) (x : X) (y : Y) : Original_LF__DOT__Poly_LF_Poly_prod X Y :=
  Original_LF__DOT__Poly_LF_Poly_prod.pair x y

-- combine function
def Original_LF__DOT__Poly_LF_Poly_combine (X Y : Type) : 
  Original_LF__DOT__Poly_LF_Poly_list X → 
  Original_LF__DOT__Poly_LF_Poly_list Y → 
  Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_prod X Y) :=
  fun lx ly =>
    match lx with
    | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
    | Original_LF__DOT__Poly_LF_Poly_list.cons x tx =>
      match ly with
      | Original_LF__DOT__Poly_LF_Poly_list.nil => Original_LF__DOT__Poly_LF_Poly_list.nil
      | Original_LF__DOT__Poly_LF_Poly_list.cons y ty =>
        Original_LF__DOT__Poly_LF_Poly_list.cons 
          (Original_LF__DOT__Poly_LF_Poly_prod.pair x y) 
          (Original_LF__DOT__Poly_LF_Poly_combine X Y tx ty)

-- split function
def Original_LF__DOT__Tactics_LF_Tactics_split (X Y : Type) :
  Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_prod X Y) → 
  Original_LF__DOT__Poly_LF_Poly_prod (Original_LF__DOT__Poly_LF_Poly_list X) (Original_LF__DOT__Poly_LF_Poly_list Y) :=
  fun l =>
    match l with
    | Original_LF__DOT__Poly_LF_Poly_list.nil => 
        Original_LF__DOT__Poly_LF_Poly_prod.pair 
          Original_LF__DOT__Poly_LF_Poly_list.nil 
          Original_LF__DOT__Poly_LF_Poly_list.nil
    | Original_LF__DOT__Poly_LF_Poly_list.cons (Original_LF__DOT__Poly_LF_Poly_prod.pair x y) t =>
        match Original_LF__DOT__Tactics_LF_Tactics_split X Y t with
        | Original_LF__DOT__Poly_LF_Poly_prod.pair lx ly =>
            Original_LF__DOT__Poly_LF_Poly_prod.pair
              (Original_LF__DOT__Poly_LF_Poly_list.cons x lx)
              (Original_LF__DOT__Poly_LF_Poly_list.cons y ly)

-- combine_split axiom (Admitted in original Rocq)
axiom Original_LF__DOT__Tactics_LF_Tactics_combine__split : 
  (X Y : Type) → 
  (l : Original_LF__DOT__Poly_LF_Poly_list (Original_LF__DOT__Poly_LF_Poly_prod X Y)) →
  (l1 : Original_LF__DOT__Poly_LF_Poly_list X) →
  (l2 : Original_LF__DOT__Poly_LF_Poly_list Y) →
  Corelib_Init_Logic_eq (Original_LF__DOT__Tactics_LF_Tactics_split X Y l) (Original_LF__DOT__Poly_LF_Poly_pair (Original_LF__DOT__Poly_LF_Poly_list X) (Original_LF__DOT__Poly_LF_Poly_list Y) l1 l2) →
  Corelib_Init_Logic_eq (Original_LF__DOT__Poly_LF_Poly_combine X Y l1 l2) l
