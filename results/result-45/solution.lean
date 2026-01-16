-- Lean 4 translation for pumping lemma and all dependencies
set_option autoImplicit false
set_option linter.all false

-- Type alias
def MyType : Type 1 := Type

-- False proposition 
inductive MyFalse : Prop where

-- True proposition
inductive MyTrue : Prop where
  | intro : MyTrue

-- Equality in Prop (becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq a a

-- Specialization of eq at Prop (needed by checker)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} (a : A) : A → Prop where
  | refl : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O := nat.O
def nat_S := nat.S
def S := nat.S
def O := nat.O
def _0 := nat.O

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

-- Our own equality type for export (the checker expects this name)
inductive LeanEq (A : Type) : A → A → Prop where
  | refl : (x : A) → LeanEq A x x

theorem nat_add_O : ∀ m : nat, LeanEq nat (nat_add nat.O m) m := fun _ => LeanEq.refl _
theorem nat_add_S : ∀ (n m : nat), LeanEq nat (nat_add (nat.S n) m) (nat.S (nat_add n m)) := fun _ _ => LeanEq.refl _

-- Disjunction (or)
inductive or (P Q : Prop) : Prop where
  | inl : P → or P Q
  | inr : Q → or P Q

def or_inl {P Q : Prop} (hp : P) : or P Q := or.inl hp
def or_inr {P Q : Prop} (hq : Q) : or P Q := or.inr hq
def or_introl {P Q : Prop} (hp : P) : or P Q := or.inl hp
def or_intror {P Q : Prop} (hq : Q) : or P Q := or.inr hq

-- Double function
def Original_LF__DOT__Induction_LF_Induction_double : nat → nat
  | nat.O => nat.O
  | nat.S n' => nat.S (nat.S (Original_LF__DOT__Induction_LF_Induction_double n'))

-- EvPlayground.ev inductive
inductive Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev nat.O
  | ev_SS : (n : nat) → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n → Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev (nat.S (nat.S n))

def Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_0 := Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.ev_0
def Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev_ev_SS := Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev.ev_SS

-- ev' inductive (alternative characterization of evenness)
inductive Original_LF__DOT__IndProp_LF_IndProp_ev' : nat → Prop where
  | ev'_0 : Original_LF__DOT__IndProp_LF_IndProp_ev' nat.O
  | ev'_2 : Original_LF__DOT__IndProp_LF_IndProp_ev' (nat.S (nat.S nat.O))
  | ev'_sum : (n m : nat) → Original_LF__DOT__IndProp_LF_IndProp_ev' n → Original_LF__DOT__IndProp_LF_IndProp_ev' m → Original_LF__DOT__IndProp_LF_IndProp_ev' (Nat_add n m)

def Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_0 := Original_LF__DOT__IndProp_LF_IndProp_ev'.ev'_0
def Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_2 := Original_LF__DOT__IndProp_LF_IndProp_ev'.ev'_2
def Original_LF__DOT__IndProp_LF_IndProp_ev'_ev'_sum := Original_LF__DOT__IndProp_LF_IndProp_ev'.ev'_sum

-- Conjunction (and)
structure and (P Q : Prop) : Prop where
  intro ::
  left : P
  right : Q

def and_intro {P Q : Prop} (hp : P) (hq : Q) : and P Q := ⟨hp, hq⟩
def and_ind {P Q : Prop} {R : Prop} (f : P → Q → R) (h : and P Q) : R := f h.left h.right

-- iff as conjunction of implications  
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

def iff_intro {A B : Prop} (h1 : A → B) (h2 : B → A) : iff A B := ⟨h1, h2⟩

-- Existential quantifier (general)
inductive ex {A : Type} (P : A → Prop) : Prop where
  | intro : (x : A) → P x → ex P

def ex_intro {A : Type} {P : A → Prop} (x : A) (h : P x) : ex P := ex.intro x h

-- Logic.Even: exists n, x = double n
def Original_LF__DOT__Logic_LF_Logic_Even (x : nat) : Prop :=
  ex (fun n => Corelib_Init_Logic_eq x (Original_LF__DOT__Induction_LF_Induction_double n))

-- not definition
def Logic_not (P : Prop) : Prop := P → MyFalse

-- excluded_middle definition (a proposition type, not an axiom)
def Original_LF__DOT__Logic_LF_Logic_excluded__middle : Prop :=
  ∀ (P : Prop), or P (P → MyFalse)

-- propositional_extensionality definition (a proposition type, not an axiom)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality : Prop :=
  ∀ (P Q : Prop), iff P Q → Corelib_Init_Logic_eq P Q

-- nor definition
def Original_LF__DOT__AltAuto_LF_AltAuto_nor (P Q : Prop) : Prop :=
  and (Logic_not P) (Logic_not Q)

-- auto_example_4 (Admitted in Original.v)
-- forall P Q R : Prop, Q -> (Q -> R) -> P \/ (Q /\ R)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_auto__example__4 :
  ∀ (P Q R : Prop), Q → (Q → R) → or P (and Q R)

-- nor_comm' (Admitted in Original.v)
-- forall (P Q : Prop), nor P Q <-> nor Q P
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__comm' :
  ∀ (P Q : Prop), iff (Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q) (Original_LF__DOT__AltAuto_LF_AltAuto_nor Q P)

-- nor_not (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not :
  ∀ (P : Prop), iff (Original_LF__DOT__AltAuto_LF_AltAuto_nor P P) (Logic_not P)

-- nor_not_or (Admitted in Original.v)
axiom Original_LF__DOT__AltAuto_LF_AltAuto_nor__not__or :
  ∀ (P Q : Prop), Original_LF__DOT__AltAuto_LF_AltAuto_nor P Q → Logic_not (or P Q)

-- ev'_ev (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_ev'__ev :
  ∀ (n : nat), iff (Original_LF__DOT__IndProp_LF_IndProp_ev' n) (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n)

-- ev_Even_iff (Admitted in Original.v)
axiom Original_LF__DOT__IndProp_LF_IndProp_ev__Even__iff :
  ∀ (n : nat), iff (Original_LF__DOT__IndProp_LF_IndProp_EvPlayground_ev n) (Original_LF__DOT__Logic_LF_Logic_Even n)

-- apply_iff_example1 (Admitted in Original.v)
-- forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R)
axiom Original_LF__DOT__Logic_LF_Logic_apply__iff__example1 :
  ∀ (P Q R : Prop), iff P Q → (Q → R) → P → R

-- not_exists_dist (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_not__exists__dist :
  Original_LF__DOT__Logic_LF_Logic_excluded__middle →
  ∀ (X : Type) (P : X → Prop), Logic_not (ex (fun x => Logic_not (P x))) → ∀ (x : X), P x

-- not_implies_our_not (Admitted in Original.v)
-- forall (P:Prop), ~ P -> (forall (Q:Prop), P -> Q)
axiom Original_LF__DOT__Logic_LF_Logic_not__implies__our__not :
  ∀ (P : Prop), Logic_not P → ∀ (Q : Prop), P → Q

-- restricted_excluded_middle_eq (Admitted in Original.v)
axiom Original_LF__DOT__Logic_LF_Logic_restricted__excluded__middle__eq :
  ∀ (n m : nat), or (Corelib_Init_Logic_eq n m) (Logic_not (Corelib_Init_Logic_eq n m))

-- contradiction_implies_anything (Admitted in Original.v)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_contradiction__implies__anything :
  ∀ (P Q : Prop), and P (Logic_not P) → Q

-- pe_implies_or_eq (Admitted in Original.v)
-- propositional_extensionality -> forall (P Q : Prop), (P \/ Q) = (Q \/ P)
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_pe__implies__or__eq :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_propositional__extensionality →
  ∀ (P Q : Prop), Corelib_Init_Logic_eq (or P Q) (or Q P)
