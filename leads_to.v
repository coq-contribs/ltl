
(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                            Solange Coupet-Grimal                         *)
(*                                                                          *)
(*                                                                          *)
(*       Laboratoire d'Informatique Fondamentale de Marseille               *)
(*               CMI-Technopole de Chateau-Gombert                          *)
(*                   39, Rue F. Joliot Curie                                *)
(*                   13453 MARSEILLE Cedex 13                               *)
(*               Solange.Coupet@cmi.univ-mrs.fr                             *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Juillet  2002                                *)
(*                                                                          *)
(****************************************************************************)
(*                                  leads_to.v                              *)
(****************************************************************************)

Section leads_to.

Require Export ltl.
Variable state label : Set.
    

Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).

(****************************************************************************)

Lemma trans_until_leads :
 forall (A B C D E : stream_formula state) (str : stream state),
 (A str -> until B C str) ->
 leads_to_via C D E str ->
 A str -> until (fun str : stream state => B str \/ D str) E str.

intros A B C D E str H_until H_always H_A.
generalize H_always; clear H_always.
unfold leads_to_via in |- *; unfold implies in |- *.
elim (H_until H_A); clear H_until H_A str.
intros str H_C H_always; inversion H_always.
rewrite H1 in H; rewrite H1.
elim (H H_C); clear H H0 H1 s0 str0 H_always H_C str.
intros str E_str; constructor 1; assumption.
intros s str D_str until_D_E until_or; constructor 2; auto.
intros s str B_str until_B_C H_always_until H_always; constructor 2; auto.
apply H_always_until; inversion H_always; assumption.
Qed.

Hint Resolve trans_until_leads.

Lemma trans_leads_to :
 forall (A B C D E : stream_formula state) (str : stream state),
 leads_to_via A B C str ->
 leads_to_via C D E str ->
 leads_to_via (fun str : stream state => A str \/ C str)
   (fun str : stream state => B str \/ D str) E str.
intros A B C D E; cofix trans_leads_to.
intro str; case str; clear str.
intros s str H1 H2; constructor.
intro H; elim H; clear H.
inversion_clear H1.
intro H_A; eauto.
inversion_clear H2.
intro H_C.
elim (H H_C); clear H.
constructor 1; auto.
constructor 2; auto.
unfold leads_to_via in trans_leads_to; unfold implies in trans_leads_to.
apply trans_leads_to.
inversion H1; assumption.
inversion H2; assumption.
Qed.

End leads_to.
