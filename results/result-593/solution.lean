-- True in Prop (using the built-in True)
def True_def : Prop := _root_.True
def True_intro : _root_.True := _root_.True.intro

-- Equality for Type arguments (exported as SProp)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

def Corelib_Init_Logic_eq_refl {A : Type} (a : A) : Corelib_Init_Logic_eq a a := Corelib_Init_Logic_eq.refl a

-- Equality for Prop arguments (exported as SProp)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

def Corelib_Init_Logic_eq_Prop_refl {A : Prop} (a : A) : Corelib_Init_Logic_eq_Prop a a := Corelib_Init_Logic_eq_Prop.refl a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def nat_O : nat := nat.O
def nat_S : nat → nat := nat.S
def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition on nat
def nat_add : nat → nat → nat
  | nat.O, n => n
  | nat.S m, n => nat.S (nat_add m n)

-- Subtraction (truncated)
def nat_sub : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S n, nat.O => nat.S n
  | nat.S n, nat.S m => nat_sub n m

-- Multiplication
def nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S m, n => nat_add n (nat_mul m n)

-- Aliases for Nat ops
def Nat_add := nat_add
def Nat_sub := nat_sub
def Nat_mul := nat_mul

-- Arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aexp : Type where
  | ANum : nat → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | APlus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMinus : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp
  | AMult : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp → Original_LF__DOT__Imp_LF_Imp_AExp_aexp

def Original_LF__DOT__Imp_LF_Imp_AExp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AExp_aexp_ANum := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum
def Original_LF__DOT__Imp_LF_Imp_AExp_aexp_APlus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus
def Original_LF__DOT__Imp_LF_Imp_AExp_aexp_AMinus := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus
def Original_LF__DOT__Imp_LF_Imp_AExp_aexp_AMult := Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult

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

def iff_intro {A B : Prop} (f : A → B) (g : B → A) : iff A B := iff.intro f g
def mp {A B : Prop} (h : iff A B) : A → B := h.mp
def mpr {A B : Prop} (h : iff A B) : B → A := h.mpr

-- Relational evaluation for arithmetic expressions
inductive Original_LF__DOT__Imp_LF_Imp_AExp_aevalR : Original_LF__DOT__Imp_LF_Imp_AExp_aexp → nat → Prop where
  | E_ANum (n : nat) : Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.ANum n) n
  | E_APlus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.APlus e1 e2) (nat_add n1 n2)
  | E_AMinus (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMinus e1 e2) (nat_sub n1 n2)
  | E_AMult (e1 e2 : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n1 n2 : nat) :
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e1 n1 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR e2 n2 →
      Original_LF__DOT__Imp_LF_Imp_AExp_aevalR (Original_LF__DOT__Imp_LF_Imp_AExp_aexp.AMult e1 e2) (nat_mul n1 n2)

-- The main theorem is admitted in Original.v, so we declare it as an axiom
axiom Original_LF__DOT__Imp_LF_Imp_AExp_aevalR__iff__aeval' :
  ∀ (a : Original_LF__DOT__Imp_LF_Imp_AExp_aexp) (n : nat),
    iff (Original_LF__DOT__Imp_LF_Imp_AExp_aevalR a n)
        (Corelib_Init_Logic_eq (Original_LF__DOT__Imp_LF_Imp_AExp_aeval a) n)
