From IsomorphismChecker Require PermittedAxiomPrinting.
From IsomorphismChecker Require Imported.

From IsomorphismChecker Require Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.
From IsomorphismChecker Require Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.
From IsomorphismChecker Require Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.

Module Type Args <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.Args := Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Args <+ Checker.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__prod__iso.Checker.

#[global] Strategy -1 [ Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.imported_Original_LF__DOT__Poly_LF_Poly_snd Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.Original_LF__DOT__Poly_LF_Poly_snd_iso ].

Module Checker (Import args : Args) <: Interface.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.Interface args
  with Definition imported_Original_LF__DOT__Poly_LF_Poly_snd := (@Imported.Original_LF__DOT__Poly_LF_Poly_snd).

Definition imported_Original_LF__DOT__Poly_LF_Poly_snd := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.imported_Original_LF__DOT__Poly_LF_Poly_snd.
Definition Original_LF__DOT__Poly_LF_Poly_snd_iso := Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__snd__iso.Original_LF__DOT__Poly_LF_Poly_snd_iso.

Section __.
#[local] Set Warnings "-masking-absolute-name".
Import PermittedAxiomPrinting.
Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Goal True. idtac "<PrintAssumptions>".
Print Assumptions Original_LF__DOT__Poly_LF_Poly_snd_iso.
idtac "</PrintAssumptions>".
Abort.
End __.


End Checker.