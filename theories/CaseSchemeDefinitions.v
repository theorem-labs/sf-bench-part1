From Stdlib Require ZArith PArith NArith.

#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Set Polymorphic Inductive Cumulativity.

Class CaseScheme@{s s'|u u' u''|} {T : Type@{s|u}} (A : T) (sort : Type@{u''}) {S : Type@{s'|u'}} (scheme : S) := {}.
#[global] Hint Mode CaseScheme - + + - - : typeclass_instances.
#[global] Hint Mode CaseScheme - - - + + : typeclass_instances.
#[global] Arguments Build_CaseScheme {T A sort S} scheme, {T A sort S scheme}.

Scheme list_caset := Elimination for list Sort Type.
Scheme list_cases := Elimination for list Sort Set.
Scheme list_casep := Elimination for list Sort Prop.
Scheme list_casesp := Elimination for list Sort SProp.

#[global] Hint Extern 0 (CaseScheme list Set ?scheme) => unify scheme list_cases; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme list Prop ?scheme) => unify scheme list_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme list SProp ?scheme) => unify scheme list_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme list Type ?scheme) => unify scheme list_caset; exact Build_CaseScheme : typeclass_instances.

Scheme nat_caset := Elimination for nat Sort Type.
Scheme nat_cases := Elimination for nat Sort Set.
Scheme nat_casep := Elimination for nat Sort Prop.
Scheme nat_casesp := Elimination for nat Sort SProp.

#[global] Hint Extern 0 (CaseScheme nat Set ?scheme) => unify scheme nat_cases; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme nat Prop ?scheme) => unify scheme nat_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme nat SProp ?scheme) => unify scheme nat_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme nat Type ?scheme) => unify scheme nat_caset; exact Build_CaseScheme : typeclass_instances.

Scheme positive_caset := Elimination for BinNums.positive Sort Type.
Scheme positive_cases := Elimination for BinNums.positive Sort Set.
Scheme positive_casep := Elimination for BinNums.positive Sort Prop.
Scheme positive_casesp := Elimination for BinNums.positive Sort SProp.

#[global] Hint Extern 0 (CaseScheme BinNums.positive Set ?scheme) => unify scheme positive_cases; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.positive Prop ?scheme) => unify scheme positive_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.positive SProp ?scheme) => unify scheme positive_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.positive Type ?scheme) => unify scheme positive_caset; exact Build_CaseScheme : typeclass_instances.

Scheme Z_caset := Elimination for BinInt.Z Sort Type.
Scheme Z_cases := Elimination for BinInt.Z Sort Set.
Scheme Z_casep := Elimination for BinInt.Z Sort Prop.
Scheme Z_casesp := Elimination for BinInt.Z Sort SProp.

#[global] Hint Extern 0 (CaseScheme BinInt.Z Set ?scheme) => unify scheme Z_cases; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinInt.Z Prop ?scheme) => unify scheme Z_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinInt.Z SProp ?scheme) => unify scheme Z_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinInt.Z Type ?scheme) => unify scheme Z_caset; exact Build_CaseScheme : typeclass_instances.

Scheme N_caset := Elimination for BinNums.N Sort Type.
Scheme N_cases := Elimination for BinNums.N Sort Set.
Scheme N_casep := Elimination for BinNums.N Sort Prop.
Scheme N_casesp := Elimination for BinNums.N Sort SProp.

#[global] Hint Extern 0 (CaseScheme BinNums.N Set ?scheme) => unify scheme N_cases; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.N Prop ?scheme) => unify scheme N_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.N SProp ?scheme) => unify scheme N_casesp; exact Build_CaseScheme : typeclass_instances.
#[global] Hint Extern 0 (CaseScheme BinNums.N Type ?scheme) => unify scheme N_caset; exact Build_CaseScheme : typeclass_instances.
