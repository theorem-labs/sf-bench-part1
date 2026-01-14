-- Translation of nat, S, ev, ex, and ex_ev_Sn

-- Define nat as an alias to avoid large Lean stdlib exports
inductive nat : Type where
  | zero : nat
  | succ : nat -> nat

-- Aliases for names
def _0 : nat := nat.zero
def S : nat → nat := nat.succ

-- The ev predicate: ev n holds when n is even
-- Using Prop (exports to SProp in Rocq)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.zero
  | ev_SS : forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.succ (nat.succ n))

-- Existential type (Props.ex in Original.v)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A -> Prop) : Prop where
  | ex_intro : forall x : A, P x -> Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- The axiom: there exists n such that ev (S n)
-- This is Admitted in Original.v, so we use an axiom
axiom Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex__ev__Sn : 
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun n : nat => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (S n))
