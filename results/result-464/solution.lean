-- Lean translation for test_anon_fun' and its dependencies

-- True in Prop (will become SProp when imported)
inductive PTrue : Prop where
  | intro : PTrue

-- Equality in Prop (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality for Prop types (also becomes SProp when imported)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- Addition
def Nat_add : nat → nat → nat
  | nat.O, m => m
  | nat.S p, m => nat.S (Nat_add p m)

-- Multiplication
def Nat_mul : nat → nat → nat
  | nat.O, _ => nat.O
  | nat.S p, m => Nat_add m (Nat_mul p m)

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- test_anon_fun' is Admitted in Original.v, so we make it an axiom
-- The statement is: doit3times (fun n => n * n) 2 = 256
-- 256 = 2^8. We build it as repeated multiplication: 2*2=4, 4*4=16, 16*16=256
-- Actually ((2^2)^2)^2 = 256

-- Build nat 256 explicitly
def nat_2 : nat := nat.S (nat.S nat.O)
def nat_4 : nat := Nat_mul nat_2 nat_2  -- 4
def nat_16 : nat := Nat_mul nat_4 nat_4  -- 16
def nat_256 : nat := Nat_mul nat_16 nat_16  -- 256

axiom Original_LF__DOT__Poly_LF_Poly_test__anon__fun' : 
  Corelib_Init_Logic_eq 
    (Original_LF__DOT__Poly_LF_Poly_doit3times nat (fun x => Nat_mul x x) nat_2)
    nat_256
