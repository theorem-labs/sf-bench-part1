-- Lean 4 translation for test_plus3'' and dependencies
set_option autoImplicit false

-- True in Prop - we need to define our own because Lean's True is already defined
-- and we need specific constructor names
inductive PTrue : Prop where
  | intro : PTrue

-- Alias for PTrue.intro  
def PTrue_intro : PTrue := PTrue.intro

namespace Wrapper
-- Export True as a definition to get the proper name in Rocq
def True : Prop := PTrue
def True_intro : True := PTrue.intro
end Wrapper

-- Equality in Prop for Type arguments (so it becomes SProp when imported)
inductive Corelib_Init_Logic_eq {A : Type} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq a a

-- Equality in Prop for Prop arguments (for SProp in Rocq)
inductive Corelib_Init_Logic_eq_Prop {A : Prop} : A → A → Prop where
  | refl (a : A) : Corelib_Init_Logic_eq_Prop a a

-- Natural numbers
inductive nat : Type where
  | O : nat
  | S : nat → nat

def _0 : nat := nat.O
def S : nat → nat := nat.S

-- plus function from LF.Basics (recursive)
def Original_LF__DOT__Basics_LF_Basics_plus : nat → nat → nat
  | nat.O, m => m
  | nat.S n', m => nat.S (Original_LF__DOT__Basics_LF_Basics_plus n' m)

-- doit3times: applies f three times
def Original_LF__DOT__Poly_LF_Poly_doit3times (X : Type) (f : X → X) (n : X) : X :=
  f (f (f n))

-- test_plus3'' is Admitted, so we axiomatize it
-- The statement is: doit3times (plus 3) 0 = 9
-- Note: (plus 3) means (Original_LF__DOT__Basics_LF_Basics_plus (S (S (S O))))
axiom Original_LF__DOT__Poly_LF_Poly_test__plus3'' :
  Corelib_Init_Logic_eq
    (Original_LF__DOT__Poly_LF_Poly_doit3times nat 
      (fun x => Original_LF__DOT__Basics_LF_Basics_plus (nat.S (nat.S (nat.S nat.O))) x) 
      _0)
    (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S (nat.S nat.O)))))))))
