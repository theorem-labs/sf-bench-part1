-- True in Prop
def True_def : Prop := _root_.True

-- Equality for Type arguments (exported as SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop arguments (exported as SProp)
inductive Corelib_Init_Logic_eq_Prop (A : Prop) : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop A a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S n, m => nat.S (nat_add n m)

-- Subtraction on nat
def nat_sub : nat → nat → nat
  | n, nat.O => n
  | nat.O, _ => nat.O
  | nat.S n, nat.S m => nat_sub n m

-- Multiplication on nat
def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, m => nat_add m (nat_mul n m)

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus

-- Evaluation function for arithmetic expressions
def Original_LF__DOT__Imp_LF_Imp_AExp_aeval : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus a1 a2 => nat_add (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus a1 a2 => nat_sub (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult a1 a2 => nat_mul (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)

-- iff as a structure (record with primitive projections)
structure iff (A B : Prop) : Prop where
  intro ::
  mp : A → B
  mpr : B → A

-- Relational evaluation for arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum : ∀ (n : nat), Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus : ∀ (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (nat_add n1 n2)
  | E_AMinus : ∀ (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (nat_sub n1 n2)
  | E_AMult : ∀ (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat),
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (nat_mul n1 n2)

-- The main theorem is admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval :
  ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : nat),
    iff (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR a n)
        (Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a) n)
