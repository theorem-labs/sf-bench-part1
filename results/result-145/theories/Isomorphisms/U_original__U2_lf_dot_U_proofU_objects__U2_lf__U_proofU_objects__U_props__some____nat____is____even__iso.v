From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Require Import Stdlib.Logic.ProofIrrelevance.

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__U_props__ex__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even.

(* The isomorphism is between two propositions (Prop and SProp), both inhabited.
   Since we have an isomorphism between the types (via ex_iso), we just need to show
   that the specific values correspond. For Prop/SProp isomorphisms, the to_from
   direction is trivial (SProp has proof irrelevance built in), and for from_to
   we use proof_irrelevance on the Prop side. *)

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even_iso : rel_iso
    {|
      to :=
        Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n)
          (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H)
          (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso hx);
      from :=
        from
          (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n)
             (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso hx));
      to_from :=
        fun x : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H) =>
        to_from
          (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n)
             (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H)
             (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso hx))
          x;
      from_to :=
        fun x : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n) =>
        seq_p_of_t
          (from_to
             (Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso (fun n : nat => Original.LF_DOT_ProofObjects.LF.ProofObjects.ev n)
                (fun H : imported_nat => imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev H)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) => Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso hx))
             x)
    |} Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.some_nat_is_even imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even.
Proof.
  unfold rel_iso.
  (* Both some_nat_is_even and imported_some_nat_is_even are proofs of isomorphic Prop/SProp types.
     Since both types are propositions, we just need to show the to direction maps the original 
     to the imported version (which it does by construction since both are inhabited). *)
  (* The to_from side (in SProp) is automatically satisfied. *)
  (* For rel_iso on propositions, we need eq (to original) imported *)
  (* Both are in SProp, so this is trivial by SProp irrelevance. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.some_nat_is_even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.some_nat_is_even Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.some_nat_is_even Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_some__nat__is__even_iso := {}.