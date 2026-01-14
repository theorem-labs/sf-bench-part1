-- True in Prop
-- Use the builtin True to get proper export name
def True_def : Prop := _root_.True

-- Equality in Prop (exported as SProp in Rocq) - for Type arguments
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (will be SProp → SProp → SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def Nat_add : nat → nat → nat
  | nat.O, n => n
  | nat.S m, n => nat.S (Nat_add m n)

-- Subtraction (truncated)
def Nat_sub : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, nat.O => nat.S n
  | nat.S n, nat.S m => Nat_sub n m

-- Multiplication
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, n => Nat_add n (Nat_mul m n)

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
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus a1 a2 => Nat_add (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus a1 a2 => Nat_sub (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult a1 a2 => Nat_mul (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a1) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a2)

-- optimize_0plus: removes additions of 0 from the left
def Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum nat.O) e2 => Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)
  | Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2 => Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e1) (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus e2)

-- The soundness theorem (admitted in Original.v, so we use an axiom)
axiom Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus__sound' : ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp),
  Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval (Original_LF__DOT__Imp_LF_Imp_AExp_optimize__0plus a)) (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a)
