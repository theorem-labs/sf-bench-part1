-- Translation of nat, ev, and ev_plus2'

-- Define nat as an alias to avoid large Lean stdlib exports
inductive nat : Type where
  | zero : nat
  | succ : nat -> nat

-- Define addition on nat
def nat.add : nat -> nat -> nat
  | nat.zero, m => m
  | nat.succ n, m => nat.succ (nat.add n m)

instance : Add nat where
  add := nat.add

-- The ev predicate: ev n holds when n is even
-- Using Prop (exports to SProp in Rocq)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.zero
  | ev_SS : forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.succ (nat.succ n))

-- ev_plus2' is the statement: forall n, forall (_ : ev n), ev (n + 2)
-- In Lean, this is definitionally the same as ev n -> ev (n + 2)
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus2' : Prop :=
  forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.add n (nat.succ (nat.succ nat.zero)))
