-- Translation of nat, aexp, and aevalR from Rocq

-- nat
inductive nat : Type where
  | O : nat
  | S : nat -> nat

-- aexp type with division
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp : Type where
  | ANum : nat -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp
  | ADiv : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp

-- Arithmetic operations on nat
def add : nat -> nat -> nat
  | nat.O, n => n
  | nat.S m, n => nat.S (add m n)

def sub : nat -> nat -> nat
  | nat.O, _ => nat.O
  | m, nat.O => m
  | nat.S m, nat.S n => sub m n

def mul : nat -> nat -> nat
  | nat.O, _ => nat.O
  | nat.S m, n => add n (mul m n)

-- Greater than
inductive gt : nat -> nat -> Prop where
  | gt_succ : forall n, gt (nat.S n) nat.O
  | gt_step : forall m n, gt m n -> gt (nat.S m) (nat.S n)

-- aevalR evaluation relation
inductive Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp -> nat -> Prop where
  | E_ANum : forall (n : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ANum n) n
  | E_APlus : forall (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.APlus a1 a2) (add n1 n2)
  | E_AMinus : forall (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMinus a1 a2) (sub n1 n2)
  | E_AMult : forall (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.AMult a1 a2) (mul n1 n2)
  | E_ADiv : forall (a1 a2 : Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp) (n1 n2 n3 : nat),
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a1 n1 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR a2 n2 ->
      gt n2 nat.O ->
      mul n2 n3 = n1 ->
      Original_LF__DOT__Imp_LF_Imp_aevalR__division_aevalR (Original_LF__DOT__Imp_LF_Imp_aevalR__division_aexp.ADiv a1 a2) n3
