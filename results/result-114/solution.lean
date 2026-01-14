-- Translation of ev and ev_plus2'' from Original.v

-- Define nat as an alias for Nat
def nat : Type := Nat
def nat_O : nat := Nat.zero
def nat_S : nat → nat := Nat.succ

-- Define addition for nat
def nat_add (n m : nat) : nat := Nat.add n m

-- Define ev : nat -> Prop (needs to be Prop so ev_plus2'' can be Prop)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat → Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat_O
  | ev_SS : ∀ (n : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → 
            Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat_S (nat_S n))

-- Define ev_plus2'' : Prop := forall n, ev n -> ev (n + 2)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2'' : Prop :=
  ∀ (n : nat), Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n → 
               Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat_add n (nat_S (nat_S nat_O)))
