-- Translation of nat, ev, ev_plus4''

-- Define nat as an alias to avoid large Lean stdlib exports
inductive nat : Type where
  | zero : nat
  | succ : nat -> nat

-- Aliases for names
def _0 : nat := nat.zero
def S : nat → nat := nat.succ

-- Define addition on nat
def Nat_add : nat -> nat -> nat
  | nat.zero, m => m
  | nat.succ n, m => nat.succ (Nat_add n m)

-- The ev predicate: ev n holds when n is even
-- Using Prop (exports to SProp in Rocq)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.zero
  | ev_SS : forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.succ (nat.succ n))

-- ev_plus4'' : for any n with ev n, we have ev (4 + n)
-- This is defined as: ev_SS (S (S n)) (ev_SS n H)
-- 4 + n = S (S (S (S n)))
def Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__plus4'' (n : nat) (H : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n) : 
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (Nat_add (S (S (S (S _0)))) n) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS (nat.succ (nat.succ n)) 
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS n H)
