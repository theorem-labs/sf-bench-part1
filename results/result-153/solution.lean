-- Translation of nat, ev, ev', and ev_ev'

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

-- The ev' predicate: alternative definition of evenness
-- ev' 0, ev' 2, and ev' (n + m) if ev' n and ev' m
inductive Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' : nat -> Prop where
  | ev'_0 : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' nat.zero
  | ev'_2 : Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' (nat.succ (nat.succ nat.zero))
  | ev'_sum : forall n m : nat, Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' n -> Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' m -> Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' (nat.add n m)

-- ev_ev' is the theorem that ev n -> ev' n (admitted in Original.v)
-- We declare it as an axiom since it's admitted
axiom Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev__ev' : forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__IndPrinciples_LF_IndPrinciples_ev' n
