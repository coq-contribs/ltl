(****************************************************************************)
(*                                                                          *)
(*                                                                          *)
(*                        Solange Coupet-Grimal                             *)
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
(*                                Juin 2002                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                 ltl .v                                   *)
(****************************************************************************)

Section ltl.

Require Export Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Variables (state : Set) (label : Set) (init_state : state -> Prop)
  (transition : label -> relation state) (fair : label -> Prop). 

(**************************** transitions  **********************************)

Inductive step (s t : state) : Prop :=
    C_trans : forall a : label, transition a s t -> step s t.

Inductive enabled (r : relation state) (s : state) : Prop :=
    c_pos_trans : forall t : state, r s t -> enabled r s.

Inductive none_or_one_step (s : state) : state -> Prop :=
  | none : none_or_one_step s s
  | one : forall t : state, step s t -> none_or_one_step s t.


(********************************** Streams *********************************)

CoInductive stream : Set :=
    cons_str : state -> stream -> stream.

Definition head_str (str : stream) : state :=
  match str with
  | cons_str s _ => s
  end.

Definition tl_str (str : stream) : stream :=
  match str with
  | cons_str _ tl => tl
  end.

Definition stream_formula := stream -> Prop.

Definition state_formula := state -> Prop. 

Definition state2stream_formula (P : state_formula) : stream_formula :=
  fun str => P (head_str str).

Definition and (P Q : stream_formula) : stream_formula :=
  fun str => P str /\ Q str.

Definition and_state (P Q : state_formula) : state_formula :=
  fun s => P s /\ Q s.

Definition leads_to (P Q : state_formula) : Prop :=
  forall s t : state, P s -> step s t -> Q t.

(****************************** LTL basic operators *************************)

Definition next (P : stream_formula) : stream_formula :=
  fun str => P (tl_str str).

CoInductive always (P : stream_formula) : stream -> Prop :=
    C_always :
      forall (s0 : state) (str : stream),
      P (cons_str s0 str) -> always P str -> always P (cons_str s0 str).

Definition trace : stream -> Prop :=
  always
    (fun str : stream =>
     none_or_one_step (head_str str) (head_str (tl_str str))).
            
Definition run (str : stream) : Prop :=
  init_state (head_str str) /\ trace str.

Inductive eventually (P : stream_formula) : stream -> Prop :=
  | ev_h : forall str : stream, P str -> eventually P str
  | ev_t :
      forall (s : state) (str : stream),
      eventually P str -> eventually P (cons_str s str).

Inductive until (P Q : stream_formula) : stream -> Prop :=
  | until_h : forall str : stream, Q str -> until P Q str
  | until_t :
      forall (s : state) (str : stream),
      P (cons_str s str) -> until P Q str -> until P Q (cons_str s str).

CoInductive unless (P Q : stream_formula) : stream -> Prop :=
  | unless_h : forall str : stream, Q str -> unless P Q str
  | unless_t :
      forall (s : state) (str : stream),
      P (cons_str s str) -> unless P Q str -> unless P Q (cons_str s str).


(****************************** LTL derived operators ***********************)

Definition infinitely_often (P : stream_formula) : 
  stream -> Prop := always (eventually P).

Definition implies (P Q : stream_formula) : stream -> Prop :=
  always (fun str : stream => P str -> Q str).

Definition is_followed (P Q : stream_formula) (str : stream) : Prop :=
  P str -> eventually Q str.

Definition is_always_followed (P Q : stream_formula) : 
  stream -> Prop := always (is_followed P Q).

Definition eventually_permanently (P : stream_formula) : 
  stream -> Prop := eventually (always P).

Definition once_always (P Q : stream_formula) : stream -> Prop :=
  implies P (always Q).

Definition leads_to_via (P Q R : stream_formula) : 
  stream -> Prop := implies P (until Q R).

Definition once_until (P Q : stream_formula) : stream -> Prop :=
  leads_to_via P P Q.

(********************************** Fairness ********************************)

Definition fairness (a : label) (str : stream) : Prop :=
  infinitely_often (state2stream_formula (enabled (transition a))) str ->
  eventually
    (fun str : stream => transition a (head_str str) (head_str (tl_str str)))
    str.

Inductive fair_step (s1 s2 : state) : Prop :=
    c_fstep :
      forall a : label, fair a -> transition a s1 s2 -> fair_step s1 s2.

Definition fairstr : stream -> Prop :=
  infinitely_often
    (fun str =>
     enabled fair_step (head_str str) ->
     fair_step (head_str str) (head_str (tl_str str))).

Definition strong_fairstr (str : stream) : Prop :=
  always
    (eventually
       (fun str' => fair_step (head_str str') (head_str (tl_str str')))) str.
     
(************************************  Safety *******************************)

Definition invariant (P : state_formula) : Prop := leads_to P P.

Definition safe (P : stream_formula) : Prop :=
  forall str : stream, run str -> always P str.


End ltl.




