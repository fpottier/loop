Set Implicit Arguments.

(* We begin with a simple technical lemma, which can be very helpful.
   In order to prove that [s] is accessible, it is permitted to assume
   that [s] has a predecessor. Indeed, if it does not have any, then
   it is obviously accessible. *)

Lemma weaken_Acc_goal:
  forall A (step : A -> A -> Prop) (s : A),
  ((exists s', step s' s) -> Acc step s) ->
  Acc step s.
Proof.
  intros ? ? ? h. econstructor. intros s' ?.
  assert (f: exists s', step s' s). { eauto. }
  destruct (h f). eauto.
Qed.

(* This module proves that, if [step1] and [step2] are in a simulation [R]
   and if [R] is defined everywhere, then the well-foundedness of [step2]
   implies the well-foundedness of [step1]. *)

(* This is visually obvious: if there was an infinite path in [step1],
   then, by definedness (which establishes [R]) and by the simulation
   hypothesis (which preserves [R] all the way), there would be an
   infinite path in [step2]. *)

(* This result is probably a consequence of [wf_inverse_rel] in Coq's
   standard library module [Coq.Wellfounded.Inverse_Image]. Yet, the
   statement that is offered here seems clearer and easier to use. *)

Section Wf.

  Variable S1 S2 : Type.
  Variable R : S1 -> S2 -> Prop.
  Variable step1 : S1 -> S1 -> Prop.
  Variable step2 : S2 -> S2 -> Prop.

  Hypothesis simulation:
    forall s1 s2 s1',
    R s1 s2 ->
    step1 s1' s1 ->
    exists s2',
    R s1' s2' /\
    step2 s2' s2.

  Lemma Acc_simulation:
    forall s2, Acc step2 s2 -> forall s1, R s1 s2 -> Acc step1 s1.
  Proof.
    induction 1 as [ s2 _ ih ]. intros s1 hr.
    econstructor. intros s'1 h1.
    destruct (simulation hr h1) as [ s2' [ ? ? ]].
    eapply ih; eauto.
  Qed.

  (* Roughly speaking, we require that [R] be defined, that is, that
     every [s1] be related by [R] to some [s2]. More precisely, it is
     sufficient to require this only in the case where [s1] is able
     to step towards [s1']. *)

  Hypothesis definedness:
    forall s1 s1', step1 s1' s1 -> exists s2, R s1 s2.

  Lemma wf_simulation:
    well_founded step2 ->
    well_founded step1.
  Proof.
    intros hwf2 s1.
    (* We may assume that [s1] has a predecessor [s1']. *)
    eapply weaken_Acc_goal. intros [ s1' h ].
    (* This allows exploiting [definedness], which establishes [R s1 s2]. *)
    destruct (definedness h) as [ s2 ? ].
    eapply Acc_simulation. eapply hwf2. eauto.
  Qed.

End Wf.

(* The statement of [wf_simulation] can be slightly simplified when [R]
   is a function. The simulation hypothesis becomes easier to read, and
   the definedness hypothesis holds trivially. *)

Section FunWf.

  Variable S1 S2 : Type.
  Variable F : S1 -> S2.
  Variable step1 : S1 -> S1 -> Prop.
  Variable step2 : S2 -> S2 -> Prop.

  Hypothesis simulation:
    forall s1 s1',
    step1 s1' s1 ->
    step2 (F s1') (F s1).

  Lemma wf_simulation_functional:
    well_founded step2 ->
    well_founded step1.
  Proof.
    intros. eapply wf_simulation with (R := fun s1 s2 => F s1 = s2) (step2 := step2).
    { intros. subst. eauto. }
    { eauto. }
    { eauto. }
  Qed.

End FunWf.

