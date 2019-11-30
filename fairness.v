(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                            Solange Coupet-Grimal                         *)
(*                                                                          *)
(*                                                                          *)
(*           Laboratoire d'Informatique Fondamentale de Marseille           *)
(*                   CMI-Technopole de Chateau-Gombert                      *)
(*                       39, Rue F. Joliot Curie                            *)
(*                      13453 MARSEILLE Cedex 13                            *)
(*                    Solange.Coupet@cmi.univ-mrs.fr                        *)
(*                                                                          *)
(*                                                                          *)
(*                                Coq V7.0                                  *)
(*                             Juillet  2002                                *)
(*                                                                          *)
(****************************************************************************)
(*                                fairness.v                                *)
(****************************************************************************)

Section fairness.

Require Import congruence.

Variables (state label : Set) (transition : label -> relation state)
  (fair : label -> Prop).

Notation Stream := (stream state) (only parsing).
Notation Stream_formula := (stream_formula state) (only parsing).
Notation Fair_step := (fair_step transition fair) (only parsing).
Notation Fairstr := (fairstr transition fair) (only parsing).
Notation Strong_fairstr := (strong_fairstr transition fair) (only parsing).

(************************* Fairness comparison ********************************)

Lemma strong_fairstr_implies_fairstr :
 forall str : stream state,
 strong_fairstr transition fair str -> fairstr transition fair str.

unfold fairstr in |- *; unfold strong_fairstr in |- *;
 unfold infinitely_often in |- *.
intros str H_fairstr.
apply
 implies_always
  with
    (P := eventually
            (fun str' : stream state =>
             fair_step transition fair (head_str str')
               (head_str (tl_str str')))); auto.
clear H_fairstr.
generalize str; clear str; unfold implies in |- *; cofix aux.
intros str; case str; clear str.
constructor; auto.
clear aux.
intro H.
apply
 implies_eventually
  with
    (P := fun str' : stream state =>
          fair_step transition fair (head_str str') (head_str (tl_str str')));
 try assumption.
clear H.
apply lift_implies_stream; auto.
Qed.

End fairness.
