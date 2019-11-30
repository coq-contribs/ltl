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
(*                                  safety.v                                *)
(****************************************************************************)

Section safety.

Require Export ltl.
Variables (state label : Set) (transition : label -> relation state)
  (init_state : state -> Prop).


Notation Stream := (stream state) (only parsing).
Notation State_formula := (state_formula state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Invariant := (invariant transition) (only parsing).
Notation None_or_one_step := (none_or_one_step transition) (only parsing).
Notation Trace := (trace transition) (only parsing).
Notation Safe := (safe init_state transition) (only parsing).
Notation Run := (run init_state transition) (only parsing).


(***************************** Always idempotence ***************************)

Lemma always_assumption :
 forall P Q : stream_formula state,
 (forall str : stream state, always Q str -> P str) ->
 forall str : stream state, always Q str -> always P str.

intros P Q; cofix always_assumption.
intros H_Q_P str.
case str; clear str.
intros s str always_Q.
constructor; auto.
apply always_assumption; auto.
inversion always_Q; assumption.
Qed.

Hint Resolve always_assumption.

Lemma always_idempotence :
 forall (Q : stream_formula state) (str : stream state),
 always Q str -> always (always Q) str.

eauto.
Qed.

(***************************** Safety  Lemmas *******************************)

Lemma inv_clos :
 forall P : state_formula state,
 invariant transition P ->
 forall s t : state, none_or_one_step transition s t -> P s -> P t.

simple induction 2; auto.
clear H0 t; intros t Hstep Ps; apply H with (s := s); assumption.
Qed.

Lemma induct :
 forall P : state_formula state,
 invariant transition P ->
 forall str : stream state,
 trace transition str ->
 P (head_str str) -> always (state2stream_formula P) str.


intros P Inv; unfold state2stream_formula in |- *; cofix induct; intro str; case str;
 simpl in |- *.
intros h tl Htrace Hhead; constructor; try assumption.
apply induct; clear induct.
inversion Htrace; assumption.
generalize Htrace; case tl; simpl in |- *.
clear Htrace tl; intros h' tl Htrace.
inversion_clear Htrace; apply inv_clos with (s := h); assumption.
Qed.


Lemma safety :
 forall P : state_formula state,
 (forall s : state, init_state s -> P s) ->
 invariant transition P ->
 safe init_state transition (state2stream_formula P).

intros P H Inv; unfold safe in |- *.
intros T Hrun; unfold run in Hrun.
elim Hrun; clear Hrun; intros H1 H2.
apply induct; auto.
Qed.

(******************************* Run management *******************************)

Lemma always_on_run :
 forall F P I : stream_formula state,
 safe init_state transition I ->
 (forall str : stream state,
  trace transition str -> always F str -> always I str -> P str) ->
 forall str : stream state,
 run init_state transition str -> always F str -> always P str.


unfold safe in |- *; unfold run in |- *; intros F P I H_safe H str str_safe;
 elim str_safe.
intro h; clear h; cut (always I str); auto.
clear str_safe; generalize str; clear str H_safe.
cofix always_on_run.
intro str; case str; clear str.
intros s str always_I H_trace always_F.
inversion always_I.
inversion H_trace.
inversion always_F.
constructor.
2: apply always_on_run; auto. 
apply H; auto.
Qed.

Lemma trace_assumption :
 forall P : stream_formula state,
 (forall str : stream state, trace transition str -> P str) ->
 forall str : stream state, trace transition str -> always P str.

unfold trace in |- *.
intros P H str H_trace.
apply
 always_assumption
  with
    (Q := fun str : stream state =>
          none_or_one_step transition (head_str str) (head_str (tl_str str)));
 assumption.
Qed.


End safety.

