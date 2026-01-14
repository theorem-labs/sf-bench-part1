-- Translation of nat, ev, ex, and some_nat_is_even

-- Define nat as an alias to avoid large Lean stdlib exports
inductive nat : Type where
  | zero : nat
  | succ : nat -> nat

-- Aliases for names
def _0 : nat := nat.zero
def S : nat → nat := nat.succ

-- The ev predicate: ev n holds when n is even
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_ev : nat -> Prop where
  | ev_0 : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev nat.zero
  | ev_SS : forall n : nat, Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n -> Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (nat.succ (nat.succ n))

-- Existential type (Props.ex in Original.v)
inductive Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex {A : Type} (P : A -> Prop) : Prop where
  | ex_intro : forall x : A, P x -> Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex P

-- The proof that some nat is even: specifically that 4 is even
-- 4 = succ (succ (succ (succ zero)))
def _4 : nat := nat.succ (nat.succ (nat.succ (nat.succ nat.zero)))
def _2 : nat := nat.succ (nat.succ nat.zero)

-- ev_0 : ev 0
-- ev_SS 0 ev_0 : ev 2
-- ev_SS 2 (ev_SS 0 ev_0) : ev 4
def ev_4_proof : Original_LF__DOT__ProofObjects_LF_ProofObjects_ev _4 :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS _2
    (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_SS nat.zero
      Original_LF__DOT__ProofObjects_LF_ProofObjects_ev.ev_0)

def Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even :
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun n : nat => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev n) :=
  Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex.ex_intro _4 ev_4_proof
