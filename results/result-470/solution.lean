-- Lean 4 translation for the snd_fst_is_swap problem

set_option autoImplicit false

-- True in Prop
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- natprod type (pair of nats)
inductive Original_LF__DOT__Lists_LF_Lists_NatList_natprod : Type where
  | pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod

-- pair constructor
def Original_LF__DOT__Lists_LF_Lists_NatList_pair : nat → nat → Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair

-- fst function (first element)
def Original_LF__DOT__Lists_LF_Lists_NatList_fst (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x _ => x

-- snd function (second element)
def Original_LF__DOT__Lists_LF_Lists_NatList_snd (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : nat :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair _ y => y

-- swap_pair function
def Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod) : Original_LF__DOT__Lists_LF_Lists_NatList_natprod :=
  match p with
  | Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair x y => Original_LF__DOT__Lists_LF_Lists_NatList_natprod.pair y x

-- snd_fst_is_swap theorem (Admitted in original, so we use axiom)
axiom Original_LF__DOT__Lists_LF_Lists_NatList_snd__fst__is__swap : ∀ (p : Original_LF__DOT__Lists_LF_Lists_NatList_natprod),
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Lists_LF_Lists_NatList_pair
       (Original_LF__DOT__Lists_LF_Lists_NatList_snd p)
       (Original_LF__DOT__Lists_LF_Lists_NatList_fst p))
    (Original_LF__DOT__Lists_LF_Lists_NatList_swap__pair p)
