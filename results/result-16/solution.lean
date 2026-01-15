-- Lean 4 translation of Rocq aevalR_extended module

-- Use our own nat to avoid Lean stdlib issues
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat.add : nat → nat → nat
  | nat.O, n => n
  | nat.S m, n => nat.S (nat.add m n)

def nat.sub : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, nat.O => nat.S m
  | nat.S m, nat.S n => nat.sub m n

def nat.mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, n => nat.add n (nat.mul m n)

-- aexp type from aevalR_extended module
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp : Type where
  | AAny : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp

-- aevalR relation from aevalR_extended module
-- Keep as Prop - will export to SProp in Rocq
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp → nat → Prop where
  | E_Any : ∀ (n : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AAny n
  | E_ANum : ∀ (n : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.ANum n) n
  | E_APlus : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.APlus a1 a2) (nat.add n1 n2)
  | E_AMinus : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AMinus a1 a2) (nat.sub n1 n2)
  | E_AMult : ∀ (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a1 n1 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR a2 n2 →
      Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__extended_aexp.AMult a1 a2) (nat.mul n1 n2)
