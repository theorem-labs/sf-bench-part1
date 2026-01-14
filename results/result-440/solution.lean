-- Lean 4 translation for next_nat_closure_is_le and all dependencies
set_option autoImplicit false

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

-- relation type
def Original_LF_Rel_relation (X : Type) : Type := X → X → Prop

-- next_nat: the successor relation on nat
inductive Original_LF_Rel_next__nat : nat → nat → Prop where
  | nn : (n : nat) → Original_LF_Rel_next__nat n (nat.S n)

-- clos_refl_trans: reflexive-transitive closure of a relation
inductive Original_LF_Rel_clos__refl__trans {X : Type} (R : X → X → Prop) : X → X → Prop where
  | rt_step (x y : X) : R x y → Original_LF_Rel_clos__refl__trans R x y
  | rt_refl (x : X) : Original_LF_Rel_clos__refl__trans R x x
  | rt_trans (x y z : X) : Original_LF_Rel_clos__refl__trans R x y → Original_LF_Rel_clos__refl__trans R y z → Original_LF_Rel_clos__refl__trans R x z

-- iff (biconditional)
structure iff (A B : Prop) : Prop where
  mp : A → B
  mpr : B → A

-- le: less than or equal for nat (based on boolean)
-- To match Imported.le, we use a boolean-based definition
inductive RocqBool : Type where
  | false : RocqBool
  | true : RocqBool

def Bool_false : RocqBool := RocqBool.false
def Bool_true : RocqBool := RocqBool.true

def nat_le : nat → nat → RocqBool
  | nat.O, _ => RocqBool.true
  | nat.S _, nat.O => RocqBool.false
  | nat.S n, nat.S m => nat_le n m

-- Equality type (will become SProp Eq in Rocq)
inductive RocqEq {A : Type} : A → A → Prop where
  | refl (a : A) : RocqEq a a

def Eq_refl {A : Type} (a : A) : RocqEq a a := RocqEq.refl a

-- le as Prop based on boolean
def le (n m : nat) : Prop := RocqEq (nat_le n m) RocqBool.true

-- next_nat_closure_is_le: Admitted in Original.v, so we use an axiom
axiom Original_LF_Rel_next__nat__closure__is__le :
  ∀ (x x0 : nat), iff (le x x0) (Original_LF_Rel_clos__refl__trans (fun (H H0 : nat) => Original_LF_Rel_next__nat H H0) x x0)
