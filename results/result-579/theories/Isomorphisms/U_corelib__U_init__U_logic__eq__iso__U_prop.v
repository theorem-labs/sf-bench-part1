From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  simpl in *.
  
  (* Define to direction *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6).
  { intro e. destruct e.
    (* Now x3 = x5, need eq x4 x6 *)
    (* H34 : IsomorphismDefinitions.eq (to x3) x4 *)
    (* H56 : IsomorphismDefinitions.eq (to x3) x6 since x3 = x5 *)
    pose proof (eq_trans (eq_sym H34) H56) as Heq.
    destruct Heq. apply Imported.Corelib_Init_Logic_eq_Prop_refl. }
  
  (* Define from direction *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> Logic.eq x3 x5).
  { intro e. destruct e.
    (* Now x4 = x6 in SProp, need x3 = x5 *)
    (* x3 = from (to x3), x5 = from (to x5) *)
    (* to x3 = x4, to x5 = x6 = x4 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Hft3: eq (from (to x3)) x3, Hft5: eq (from (to x5)) x5 *)
    (* to x3 = x4, to x5 = x6 = x4 (since we destructed e) *)
    (* So from (to x3) = from x4 = from (to x5), thus x3 = x5 *)
    pose proof (f_equal (from hx) (eq_trans H34 (eq_sym H56))) as Hf.
    (* Hf: from (to x3) = from (to x5) *)
    pose proof (eq_trans (eq_sym Hft3) (eq_trans Hf Hft5)) as H.
    apply eq_of_seq. exact H. }
  
  refine {|
    to := to_dir;
    from := from_dir;
    to_from := _;
    from_to := _
  |}.
  - (* to_from: proof irrelevance in SProp *)
    intros e. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance *)
    intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
