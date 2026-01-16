From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__reg____exp__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list : forall x : Type, imported_Original_LF__DOT__Poly_LF_Poly_list x -> imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp x := (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list).

(* Helper: prove equality directly using fixpoint *)
Fixpoint reg_exp_of_list_iso_eq {T1 T2 : Type} (hT : Iso T1 T2) 
    (l : Original.LF_DOT_Poly.LF.Poly.list T1) {struct l} :
    IsomorphismDefinitions.eq 
      (to (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hT) (Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list l))
      (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list T2 (to (Original_LF__DOT__Poly_LF_Poly_list_iso hT) l)).
Proof.
  destruct l as [| h t].
  - (* nil case *)
    simpl.
    apply IsomorphismDefinitions.eq_refl.
  - (* cons case *)
    simpl.
    apply (IsoEq.f_equal2 (fun a b => Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp_App T2 a b)).
    + apply IsomorphismDefinitions.eq_refl.
    + apply reg_exp_of_list_iso_eq.
Defined.

Instance Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2),
  rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4 ->
  rel_iso (Original_LF__DOT__IndProp_LF_IndProp_reg__exp_iso hx) (Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list x3) (imported_Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x4).
Proof.
  intros x1 x2 hx x3 x4 H34.
  pose proof (proj_rel_iso H34) as H34'.
  apply Build_rel_iso.
  pose proof (reg_exp_of_list_iso_eq hx x3) as Heq.
  (* Heq: eq (to reg_exp_iso (reg_exp_of_list x3)) (imported_reg_exp_of_list (to list_iso x3)) *)
  (* H34': eq (to list_iso x3) x4 *)
  (* Need: eq (to reg_exp_iso (reg_exp_of_list x3)) (imported_reg_exp_of_list x4) *)
  exact (match H34' in (IsomorphismDefinitions.eq _ y) return 
           IsomorphismDefinitions.eq _ (Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list x2 y) with
         | IsomorphismDefinitions.eq_refl => Heq
         end).
Defined.
Instance: KnownConstant (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_IndProp.LF.IndProp.reg_exp_of_list) (@Imported.Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list) Original_LF__DOT__IndProp_LF_IndProp_reg__exp__of__list_iso := {}.
