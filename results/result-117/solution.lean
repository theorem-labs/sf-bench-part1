-- Use a namespace to avoid conflict with Lean's built-in True
namespace Rocq

-- Translation of True (trivially true proposition) - in Prop so it becomes SProp in Rocq
inductive True : Prop where
  | I : True

end Rocq

-- Translation of eq (equality) - define in Prop so it becomes SProp in Rocq
inductive Corelib_Init_Logic_eq {X : Type} : X → X → Prop where
  | refl (x : X) : Corelib_Init_Logic_eq x x

-- trans_eq is an axiom in Original.v
-- "forall (X : Type) (n m o : X), n = m -> m = o -> n = o"
axiom Original_LF__DOT__Tactics_LF_Tactics_trans__eq : 
  ∀ (X : Type) (n m o : X), Corelib_Init_Logic_eq n m → Corelib_Init_Logic_eq m o → Corelib_Init_Logic_eq n o
