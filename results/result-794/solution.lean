-- True in Prop (will become SProp in Rocq)
abbrev MyTrue : Prop := _root_.True

-- Equality in Prop (will become SProp in Rocq)
-- This mirrors the standard Eq but in Prop
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a :=
  Corelib_Init_Logic_eq.refl a

-- Equality for Prop (will become SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Boolean type (matching LF.Basics.bool)
inductive Original_LF__DOT__Basics_LF_Basics_bool : Type where
  | true : Original_LF__DOT__Basics_LF_Basics_bool
  | false : Original_LF__DOT__Basics_LF_Basics_bool

def Original_LF__DOT__Basics_LF_Basics_true : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.true

def Original_LF__DOT__Basics_LF_Basics_false : Original_LF__DOT__Basics_LF_Basics_bool :=
  Original_LF__DOT__Basics_LF_Basics_bool.false

-- eqb function (equality test for nat)
def Original_LF__DOT__Basics_LF_Basics_eqb : nat → nat → Original_LF__DOT__Basics_LF_Basics_bool
  | nat.O, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.true
  | nat.O, nat.S _ => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S _, nat.O => Original_LF__DOT__Basics_LF_Basics_bool.false
  | nat.S n', nat.S m' => Original_LF__DOT__Basics_LF_Basics_eqb n' m'

-- The id type (wraps a natural number)
inductive Original_LF__DOT__Lists_LF_Lists_id : Type where
  | Id : nat → Original_LF__DOT__Lists_LF_Lists_id

-- The eqb_id function (equality test for id)
def Original_LF__DOT__Lists_LF_Lists_eqb__id (x1 x2 : Original_LF__DOT__Lists_LF_Lists_id) : Original_LF__DOT__Basics_LF_Basics_bool :=
  match x1, x2 with
  | Original_LF__DOT__Lists_LF_Lists_id.Id n1, Original_LF__DOT__Lists_LF_Lists_id.Id n2 =>
    Original_LF__DOT__Basics_LF_Basics_eqb n1 n2

-- natoption type
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natoption : Type where
  | Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption
  | None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption

-- None constructor alias
def Original_LF__DOT__Lists_LF_Lists_NatList_None : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None

-- Some constructor alias
def Original_LF__DOT__Lists_LF_Lists_NatList_Some : nat → Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some

-- partial_map type
inductive Original_LF__DOT__Lists_LF_Lists_partial__map : Type where
  | empty : Original_LF__DOT__Lists_LF_Lists_partial__map
  | record : Original_LF__DOT__Lists_LF_Lists_id → nat → Original_LF__DOT__Lists_LF_Lists_partial__map → Original_LF__DOT__Lists_LF_Lists_partial__map

-- update function
def Original_LF__DOT__Lists_LF_Lists_update
    (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x : Original_LF__DOT__Lists_LF_Lists_id)
    (value : nat)
    : Original_LF__DOT__Lists_LF_Lists_partial__map :=
  Original_LF__DOT__Lists_LF_Lists_partial__map.record x value d

-- find function
def Original_LF__DOT__Lists_LF_Lists_find (x : Original_LF__DOT__Lists_LF_Lists_id) (d : Original_LF__DOT__Lists_LF_Lists_partial__map) : Original_LF__DOT__Lists_LF_Lists_NatList_natoption :=
  match d with
  | Original_LF__DOT__Lists_LF_Lists_partial__map.empty =>
    Original_LF__DOT__Lists_LF_Lists_NatList_natoption.None
  | Original_LF__DOT__Lists_LF_Lists_partial__map.record y v d' =>
    match Original_LF__DOT__Lists_LF_Lists_eqb__id x y with
    | Original_LF__DOT__Basics_LF_Basics_bool.true => Original_LF__DOT__Lists_LF_Lists_NatList_natoption.Some v
    | Original_LF__DOT__Basics_LF_Basics_bool.false => Original_LF__DOT__Lists_LF_Lists_find x d'

-- update_neq theorem (admitted in Original.v, so axiom here)
axiom Original_LF__DOT__Lists_LF_Lists_update__neq :
  ∀ (d : Original_LF__DOT__Lists_LF_Lists_partial__map)
    (x y : Original_LF__DOT__Lists_LF_Lists_id)
    (o : nat),
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_eqb__id x y) Original_LF__DOT__Basics_LF_Basics_false →
    Corelib_Init_Logic_eq (Original_LF__DOT__Lists_LF_Lists_find x (Original_LF__DOT__Lists_LF_Lists_update d y o)) (Original_LF__DOT__Lists_LF_Lists_find x d)
