From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.


Definition imported_True : SProp := Imported.MyTrue.

Instance True_iso : (Iso True imported_True).
Proof.
  unshelve eapply Build_Iso.
  - intro H. exact Imported.True_intro.
  - intro H. exact I.
  - (* to_from: needs SProp eq. Since imported_True is an SProp, and both sides 
       compute to Imported.True_intro, this is eq_refl *)
    intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: needs SProp eq between True values. Since both sides compute to I, 
       this is eq_refl *)
    intro x. destruct x. apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant True := {}.
Instance: KnownConstant Imported.MyTrue := {}.
Instance: IsoStatementProofFor True True_iso := {}.
Instance: IsoStatementProofBetween True Imported.MyTrue True_iso := {}.