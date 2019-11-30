(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                            Solange Coupet-Grimal                         *)
(*                                                                          *)
(*                                                                          *)
(*           Laboratoire d'Informatique Fondamentale de Marseille           *)
(*                   CMI-Technopole de Chateau-Gombert                      *)
(*                       39, Rue F. Joliot Curie                            *)
(*                       13453 MARSEILLE Cedex 13                           *)
(*                     Solange.Coupet@cmi.univ-mrs.fr                       *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Juillet  2002                                *)
(*                                                                          *)
(****************************************************************************)
(*                              termination.v                               *)
(****************************************************************************)

Section termination.

Require Export ltl.
Require Import Relations.

Variables (Alpha : Set) (state : Set) (r : relation Alpha)
  (meas : state -> Alpha -> Prop).

Hypothesis H_wf : well_founded r.

Notation Stream := (stream state) (only parsing).
Notation State_formula := (state_formula state) (only parsing).

Lemma wf_leadsto :
 forall (A B C : state_formula state) (str : stream state),
 (forall v : Alpha,
  leads_to_via (state2stream_formula (fun s : state => A s /\ meas s v))
    (state2stream_formula B)
    (state2stream_formula
       (fun s : state => A s /\ (exists t : Alpha, meas s t /\ r t v) \/ C s))
    str) ->
 A (head_str str) /\ (exists v : Alpha, meas (head_str str) v) ->
 until (state2stream_formula B) (state2stream_formula C) str.


intros A B C str; unfold leads_to_via in |- *; unfold implies in |- *;
 intros H h; elim h; clear h.
intros A_head h; elim h; clear h.
intro v0; generalize str H A_head; clear H A_head str.
elim (H_wf v0); clear v0.
intros v0 H_acc H_rec str H A_head H_meas.
cut
 (always
    (fun str : stream state =>
     state2stream_formula (fun s : state => A s /\ meas s v0) str ->
     until (state2stream_formula B)
       (state2stream_formula
          (fun s : state =>
           A s /\ (exists t : Alpha, meas s t /\ r t v0) \/ C s)) str) str);
 auto.
intro h; inversion h; clear h.
rewrite H2; rewrite H2 in H0; generalize H1; replace str0 with (tl_str str).
2: rewrite <- H2; auto.
clear H1 H2 s0 str0; unfold state2stream_formula in H0;
 cut
  (until (fun str : stream state => B (head_str str))
     (fun str : stream state =>
      A (head_str str) /\ (exists t : Alpha, meas (head_str str) t /\ r t v0) \/
      C (head_str str)) str); try apply H0; auto.
clear H0; intro H_until; generalize H; elim H_until. 
clear H H_until A_head H_meas str; intros str H H_always H_always_v0; elim H;
 clear H.
intro H; elim H; clear H. 
intros A_head H; elim H; clear H.
intros v H; elim H; clear H.
intros H_meas H_r; apply H_rec with (y := v); auto.
constructor 1; auto.
clear H_rec H_acc H_wf H A_head H_meas H_until str.
intros s str H_B H_until H_rec H_always.
constructor 2; auto.
apply H_rec.
intro v;
 cut
  (always
     (fun str : stream state =>
      state2stream_formula (fun s : state => A s /\ meas s v) str ->
      until (state2stream_formula B)
        (state2stream_formula
           (fun s : state =>
            A s /\ (exists t : Alpha, meas s t /\ r t v) \/ C s)) str)
     (cons_str s str)); auto. 
clear H_always; intro H_always; inversion H_always; assumption.
simpl in H1; inversion H1; rewrite H2; generalize H0;
 replace str0 with (tl_str str); auto.
rewrite <- H2; auto.
Qed.

Hint Resolve wf_leadsto.

Lemma wf_leadsto_rule :
 forall (A B C : state_formula state) (str : stream state),
 (forall v : Alpha,
  leads_to_via (state2stream_formula (fun s : state => A s /\ meas s v))
    (state2stream_formula B)
    (state2stream_formula
       (fun s : state => A s /\ (exists t : Alpha, meas s t /\ r t v) \/ C s))
    str) ->
 leads_to_via
   (state2stream_formula
      (fun s : state => A s /\ (exists t : Alpha, meas s t)))
   (state2stream_formula B) (state2stream_formula C) str.

intros A B C; cofix wf_leadsto_rule.
intro str; case str; intros s tl H; constructor; eauto.
unfold leads_to_via in wf_leadsto_rule; unfold implies in wf_leadsto_rule;
 apply wf_leadsto_rule.
intro v;
 cut
  (leads_to_via (state2stream_formula (fun s : state => A s /\ meas s v))
     (state2stream_formula B)
     (state2stream_formula
        (fun s : state => A s /\ (exists t : Alpha, meas s t /\ r t v) \/ C s))
     (cons_str s tl)); auto.
unfold leads_to_via in |- *; unfold implies in |- *; intro H0;
 inversion_clear H0; assumption.
Qed.

End termination.


