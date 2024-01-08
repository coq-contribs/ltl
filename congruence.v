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
(*                    Solange.Coupet@cmi.univ-mrs.fr                        *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Juillet  2002                                *)
(*                                                                          *)
(****************************************************************************)
(*                               congruence.v                               *)
(****************************************************************************)

Require Export safety.

Section congruence.

Variables (state label : Set) (transition : label -> relation state)
  (init_state : state -> Prop).
        
Notation Stream := (stream state) (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Safe := (safe init_state transition) (only parsing).


(***************************************************************************)

Lemma lift_imp :
 forall P Q : state_formula state,
 (forall s : state, P s -> Q s) ->
 forall str : stream state,
 state2stream_formula P str -> state2stream_formula Q str.

unfold state2stream_formula in |- *; auto.
Qed.

Lemma lift_implies_stream :
 forall P Q : stream_formula state,
 (forall str : stream state, P str -> Q str) ->
 forall str : stream state, implies P Q str.
unfold implies in |- *; intros P Q H. 
cofix lift_implies_stream; intro str; case str; clear str.
intros s str; constructor; auto.
Qed.

Lemma lift_implies_state :
 forall P Q : state_formula state,
 (forall s : state, P s -> Q s) ->
 forall str : stream state,
 implies (state2stream_formula P) (state2stream_formula Q) str.

intros P Q H str; apply lift_implies_stream; clear str.
intros str H'.
apply lift_imp with (P := P); assumption.
Qed.

Lemma implies_eventually :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> eventually P str -> eventually Q str.
intros P Q str H1 H2.
generalize H1; clear H1.
elim H2; clear H2; clear str.
intros str H1 H2.
unfold implies in H2.
inversion H2.
constructor 1.
apply H.
rewrite H3; assumption.
intros s str H_P H_rec H_implies.
constructor 2.
apply H_rec.
inversion_clear H_implies.
auto.
Qed.

Lemma congruence_eventually :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> implies (eventually P) (eventually Q) str.

unfold implies in |- *; intros P Q H str.
apply
 always_assumption with (Q := fun str0 : stream state => P str0 -> Q str0);
 auto.
clear str; intros str H_always H_ev. 
apply implies_eventually with (P := P); auto.
Qed.

Lemma implies_always :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> always P str -> always Q str.


intros P Q.
cofix implies_always.
 intro str; case str; clear str.
intros s str H1 H2.
constructor.
inversion_clear H2.
inversion_clear H1.
auto.
apply implies_always.
inversion_clear H1.
auto.
inversion H2; auto.
Qed.

Lemma congruence_always :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> implies (always P) (always Q) str.
                             
unfold implies in |- *; intros P Q H str.
apply
 always_assumption with (Q := fun str0 : stream state => P str0 -> Q str0);
 auto.
clear str; intros str H_always H_al. 
apply implies_always with (P := P); auto.
Qed.


Lemma implies_infinitely_often :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> infinitely_often P str -> infinitely_often Q str.

unfold infinitely_often in |- *.
intros P Q str H_implies H_always.
apply implies_always with (P := eventually P); try assumption.
unfold implies in |- *; unfold implies in H_implies.
apply always_assumption with (Q := fun str : stream state => P str -> Q str).
intros; apply implies_eventually with (P := P) (Q := Q); auto.
assumption.
 Qed.

Lemma congruence_infinitely_often :
 forall (P Q : stream_formula state) (str : stream state),
 implies P Q str -> implies (infinitely_often P) (infinitely_often Q) str.

unfold implies in |- *; intros P Q H str.
apply
 always_assumption with (Q := fun str0 : stream state => P str0 -> Q str0);
 auto.
clear str; intros str H_always H_inf. 
apply implies_infinitely_often with (P := P); auto.
Qed.

Lemma invariant_implies :
 forall P Q I : stream_formula state,
 (forall str : stream state, always I str -> P str -> Q str) ->
 forall str : stream state, always I str -> implies P Q str.

intros P Q I H str H'.
unfold implies in |- *.
apply always_assumption with (Q := I); assumption.

Qed.


Lemma inv_implies_inf_often :
 forall P Q I : stream_formula state,
 (forall str : stream state, always I str -> P str -> Q str) ->
 forall str : stream state,
 always I str -> infinitely_often P str -> infinitely_often Q str.


intros P Q I H str Inv H_inf.
apply implies_infinitely_often with (P := P); try assumption.
apply invariant_implies with (I := I); assumption.
Qed.

Lemma implies_until :
 forall (P P' Q Q' : stream_formula state) (str : stream state),
 implies P P' str -> implies Q Q' str -> until P Q str -> until P' Q' str.

intros P P' Q Q' str HP HQ H.
generalize HP HQ; clear HP HQ.
elim H; clear H; clear str.
intros str HQ HP Himplie.
constructor 1.
inversion Himplie.
apply H.
rewrite H1; auto.
intros s str HP Huntil H_rec HIP HIQ.
constructor 2.
inversion HIP; auto.
apply H_rec.
inversion HIP; auto.
inversion HIQ; auto.
Qed.


Lemma implies_until_state :
 forall P P' Q Q' : state_formula state,
 (forall s : state, P s -> P' s) ->
 (forall s : state, Q s -> Q' s) ->
 forall str : stream state,
 until (state2stream_formula P) (state2stream_formula Q) str ->
 until (state2stream_formula P') (state2stream_formula Q') str.

intros P P' Q Q' H_P_P' H_Q_Q' str H.
apply
 implies_until
  with (P := state2stream_formula P) (Q := state2stream_formula Q);
 try assumption.
apply lift_implies_state with (P := P); assumption.
apply lift_implies_state with (P := Q); assumption.
Qed.

Lemma implies_safe :
 forall P Q : stream_formula state,
 (forall str : stream state, implies P Q str) ->
 safe init_state transition P -> safe init_state transition Q.

unfold safe in |- *.
intros P Q imp_P_Q H_P str run_str.
apply implies_always with (P := P); auto.
Qed.

End congruence.