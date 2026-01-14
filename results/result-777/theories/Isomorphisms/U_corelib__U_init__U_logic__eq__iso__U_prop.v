From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

(* For SProp, we use the imported Corelib_Init_Logic_eq_Prop *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := 
  @Imported.Corelib_Init_Logic_eq_Prop.

(* For SProp arguments, both sides are proof-irrelevant *)
Instance Corelib_Init_Logic_eq_iso_Prop : forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2),
  rel_iso hx x3 x4 ->
  forall (x5 : x1) (x6 : x2),
  rel_iso hx x5 x6 ->
  Iso (x3 = x5) (imported_Corelib_Init_Logic_eq_Prop x4 x6).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq. subst x5.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* H34 and H56 now both relate x3 to x4 and x6 respectively *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Heq46.
    exact (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w) 
             (Imported.Corelib_Init_Logic_eq_refl_inst1 x2 x4) Heq46).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> x3 = x5 *)
    intro Heq.
    (* Use the isomorphism to transport back *)
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    (* Convert imported eq to IsomorphismDefinitions.eq *)
    unfold imported_Corelib_Init_Logic_eq_Prop in Heq.
    pose proof (Imported.Corelib_Init_Logic_eq_inst1_indl x2 x4 
                  (fun z _ => IsomorphismDefinitions.eq x4 z) 
                  IsomorphismDefinitions.eq_refl x6 Heq) as Heq46.
    pose proof (IsoEq.f_equal (from hx) Heq46) as HfromHeq.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from: forall y, eq (to (from y)) y -- in SProp, this is trivial *)
    intro. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x, eq (from (to x)) x *)
    intro Heq. destruct Heq. apply IsomorphismDefinitions.eq_refl.
Defined.
