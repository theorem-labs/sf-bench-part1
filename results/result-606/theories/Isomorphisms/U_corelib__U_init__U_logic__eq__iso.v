From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From Stdlib.Logic Require Import ProofIrrelevance.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* We define imported_Corelib_Init_Logic_eq as the Imported version which is now in SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Lift Prop equality to SProp equality *)
Definition prop_to_sprop_eq {A : Prop} {x y : A} (H : x = y) : IsomorphismDefinitions.eq x y :=
  match H in Corelib.Init.Logic.eq _ a return IsomorphismDefinitions.eq x a with
  | Corelib.Init.Logic.eq_refl => IsomorphismDefinitions.eq_refl
  end.

(* SProp proof irrelevance for Prop terms *)
Definition sprop_proof_irrelevance {A : Prop} (x y : A) : IsomorphismDefinitions.eq x y :=
  prop_to_sprop_eq (proof_irrelevance A x y).

(* Helper to transport Imported SProp equality along another SProp equality *)
Definition transport_imported_1 {A : Type} {x y z : A} 
    (H1 : IsomorphismDefinitions.eq x y) 
    (H2 : IsomorphismDefinitions.eq x z) : Imported.Corelib_Init_Logic_eq A y z :=
  match H1 in IsomorphismDefinitions.eq _ w return Imported.Corelib_Init_Logic_eq A w z with
  | IsomorphismDefinitions.eq_refl => 
      match H2 in IsomorphismDefinitions.eq _ v return Imported.Corelib_Init_Logic_eq A x v with
      | IsomorphismDefinitions.eq_refl => Imported.Corelib_Init_Logic_eq_refl A x
      end
  end.

Definition transport_imported_2 {A : Type} {x y z : A}
    (H1 : IsomorphismDefinitions.eq y z)
    (H2 : IsomorphismDefinitions.eq x y) : Imported.Corelib_Init_Logic_eq A x z :=
  match H1 in IsomorphismDefinitions.eq _ w return Imported.Corelib_Init_Logic_eq A x w with
  | IsomorphismDefinitions.eq_refl => 
      match H2 in IsomorphismDefinitions.eq _ v return Imported.Corelib_Init_Logic_eq A x v with
      | IsomorphismDefinitions.eq_refl => Imported.Corelib_Init_Logic_eq_refl A x
      end
  end.

(* Helper function to derive Prop equality from Imported SProp equalities *)
Definition derive_prop_eq_imported {A B : Type} (iso : Iso A B) 
    (x3 x5 : A) (x4 x6 : B)
    (Hx34 : IsomorphismDefinitions.eq (to iso x3) x4)
    (Hx56 : IsomorphismDefinitions.eq (to iso x5) x6)
    (Heq : Imported.Corelib_Init_Logic_eq B x4 x6) : Corelib.Init.Logic.eq x3 x5 :=
  let H1 : IsomorphismDefinitions.eq (from iso x4) x3 :=
    match Hx34 in IsomorphismDefinitions.eq _ z 
          return IsomorphismDefinitions.eq (from iso (to iso x3)) x3 -> 
                 IsomorphismDefinitions.eq (from iso z) x3 with
    | IsomorphismDefinitions.eq_refl => fun H => H
    end (from_to iso x3) in
  let H2 : IsomorphismDefinitions.eq (from iso x6) x5 :=
    match Hx56 in IsomorphismDefinitions.eq _ z
          return IsomorphismDefinitions.eq (from iso (to iso x5)) x5 ->
                 IsomorphismDefinitions.eq (from iso z) x5 with
    | IsomorphismDefinitions.eq_refl => fun H => H
    end (from_to iso x5) in
  match Heq in Imported.Corelib_Init_Logic_eq _ _ z
        return IsomorphismDefinitions.eq (from iso x4) x3 -> 
               IsomorphismDefinitions.eq (from iso z) x5 -> 
               Corelib.Init.Logic.eq x3 x5 with
  | Imported.Corelib_Init_Logic_eq_refl _ _ => 
      fun (Ha : IsomorphismDefinitions.eq (from iso x4) x3) 
          (Hb : IsomorphismDefinitions.eq (from iso x4) x5) =>
        match Ha in IsomorphismDefinitions.eq _ a 
              return IsomorphismDefinitions.eq (from iso x4) x5 -> a = x5 with
        | IsomorphismDefinitions.eq_refl => 
            fun Hb' => match Hb' with IsomorphismDefinitions.eq_refl => Corelib.Init.Logic.eq_refl end
        end Hb
  end H1 H2.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold imported_Corelib_Init_Logic_eq, rel_iso in *.
  (* Hx34 : IsomorphismDefinitions.eq (hx x3) x4 *)
  (* Hx56 : IsomorphismDefinitions.eq (hx x5) x6 *)
  (* Need: Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq x2 x4 x6) *)
  apply Build_Iso with
    (to := fun H : Corelib.Init.Logic.eq x3 x5 => 
             let Hmid := transport_imported_1 Hx34
               (match H in Corelib.Init.Logic.eq _ y return IsomorphismDefinitions.eq (hx x3) (hx y) with
                | Corelib.Init.Logic.eq_refl => IsomorphismDefinitions.eq_refl
                end) in
             match Hx56 in IsomorphismDefinitions.eq _ z 
                   return Imported.Corelib_Init_Logic_eq x2 x4 (hx x5) ->
                          Imported.Corelib_Init_Logic_eq x2 x4 z with
             | IsomorphismDefinitions.eq_refl => fun H' => H'
             end Hmid)
    (from := fun (Heq : Imported.Corelib_Init_Logic_eq x2 x4 x6) => 
               @derive_prop_eq_imported x1 x2 hx x3 x5 x4 x6 Hx34 Hx56 Heq).
  - intros. apply IsomorphismDefinitions.eq_refl.
  - intros x.
    (* Need to show: eq (derive_prop_eq_imported ... (to x)) x *)
    (* This is an SProp equality between two Prop proofs of x3 = x5 *)
    (* Use proof irrelevance lifted to SProp *)
    apply sprop_proof_irrelevance.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@imported_Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@imported_Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Also export the Prop version for the checker *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.
