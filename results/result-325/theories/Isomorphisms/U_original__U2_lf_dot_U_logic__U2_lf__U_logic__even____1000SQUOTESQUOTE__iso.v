From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Isomorphisms.U_s__iso.

(* Show that n1000 = imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0))) *)
Lemma n1000_eq : Imported.n1000 = imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0))).
Proof.
  unfold imported_S, imported_0.
  vm_compute. reflexivity.
Qed.

Definition imported_Original_LF__DOT__Logic_LF_Logic_even__1000'' : 
  imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (iterate1 imported_S 997 imported_0)))).
Proof.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  rewrite <- n1000_eq.
  exact Imported.Original_LF__DOT__Logic_LF_Logic_even__1000''.
Defined.

(* The isomorphism between the two axioms *)
(* Both are in SProp, so all elements are equal *)

Instance Original_LF__DOT__Logic_LF_Logic_even__1000''_iso : rel_iso 
    (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 997 O imported_0 _0_iso))))) 
    Original.LF_DOT_Logic.LF.Logic.even_1000''
    imported_Original_LF__DOT__Logic_LF_Logic_even__1000''.
Proof.
  unfold rel_iso. simpl.
  exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.even_1000'' := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_even__1000'' := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_1000'' Original_LF__DOT__Logic_LF_Logic_even__1000''_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_1000'' Imported.Original_LF__DOT__Logic_LF_Logic_even__1000'' Original_LF__DOT__Logic_LF_Logic_even__1000''_iso := {}.