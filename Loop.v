Set Implicit Arguments.
Require Import MyWf.

(* This module helps define a simple [do/while] loop in Coq. *)

(* It is currently organized in three main sections: *)

(* 1. [Loop] covers the simple case where the proof of termination does not
   rely on an invariant (or, if it does, this is opaque to us -- the invariant
   must be built in the type [S]). Thus, one must establish termination before
   one can use the [loop] combinator, which constructs the loop.

   Also in this section, [loop_eq] proves that the loop thus defined is indeed
   a fixed point, and [loop_invariant] offers a reasoning rule in the style of
   Hoare, which allows proving that a loop invariant holds. *)

(* 2. [LoopWithInvariant] covers the case where the proof of termination relies
   on an invariant. In that case, one must provide the invariant and prove that
   the invariant implies termination before one can use [loop_with_invariant],
   which constructs the loop. *)

(* 3. [Refinement] offers a facility to define a new loop as a refinement of
   an existing loop, without being forced to re-establish the termination of
   the new loop. *)

(* We mark definitions PRIVATE when we believe that they are of no use to the
   end user and PUBLIC when they are intended to be useful to the end user. *)

(* ---------------------------------------------------------------------------- *)

(* A loop body expects a state and produces a message, which is a new state
   together with an indication of whether the loop should terminate or
   continue. *)

(* PUBLIC *)
Inductive message S T :=
| MsgContinue: S -> message S T
| MsgFinished: T -> message S T.

Arguments MsgContinue { S T } _.
Arguments MsgFinished { S T } _.

(* This tactic simplifies an equality hypothesis between two messages. *)

(* PUBLIC *)
Ltac msg_injection :=
  match goal with
  | h: MsgContinue _ = MsgContinue _ |- _ =>
      injection h; intro; try subst; first [ clear h | generalize h ]
  | h: MsgFinished _ = MsgFinished _ |- _ =>
      injection h; intro; try subst; first [ clear h | generalize h ]
  end.

(* Equality of messages is parameterized with notions of equality at types [S]
   and [T]. *)

(* PUBLIC *)
Inductive message_eq
  (S1 T1 S2 T2 : Type)
  (RS : S1 -> S2 -> Prop)
  (RT : T1 -> T2 -> Prop)
: message S1 T1 -> message S2 T2 -> Prop :=
| MessageEqContinue:
    forall s1 s2,
    RS s1 s2 ->
    message_eq RS RT (MsgContinue s1) (MsgContinue s2)
| MessageEqFinished:
    forall t1 t2,
    RT t1 t2 ->
    message_eq RS RT (MsgFinished t1) (MsgFinished t2).

(* ---------------------------------------------------------------------------- *)

Section Loop.

  (* We assume we are operating on a state of type [S]. The final state --
     where the loop has stopped -- can be of a different type [T]. *)

  Context { S T : Type }.

  Variable body : S -> message S T.

  (* In order to argue that the loop terminates, we expect a
     well-founded ordering [evolution], together with a proof
     that, when the loop body says Continue, the new state is
     related to (i.e., smaller than) the previous state. *)

  Context { evolution : S -> S -> Prop }.

  Hypothesis wf_evolution : well_founded evolution.

  Hypothesis body_evolution:
    forall s s',
    body s = MsgContinue s' ->
    evolution s' s.

  (* For some reason, expanding [body_evolution] as follows
     helps [destruct] in tricky situations, e.g. in the proof
     of [loop_eq]. *)

  (* PRIVATE *)
  Lemma body_evolution_expanded:
    forall s m,
    body s = m ->
    forall s',
    m = MsgContinue s' ->
    evolution s' s.
  Proof.
    intros. subst. eapply body_evolution. assumption.
  Qed.

  (* Here is the code for the loop. *)

  (* PUBLIC *)
  Definition loop : S -> T :=
    (* The definition is by well-founded induction on the state,
       for the ordering [evolution]. *)
    Fix wf_evolution (fun _ : S => T) (fun (s : S)
    (loop : forall s', evolution s' s -> T) =>
      (* Run one step of the algorithm by calling [body s]
         and inspect the resulting message [m]. Keep track of
         the equality [body s = m] under the name [h]. *)
      match body s as m return (body s = m -> T) with
      (* If [body] says we must continue, loop. Applying the lemma
         [body_evolution] to the equality [h] provides a proof of
         [evolution s' s], which justifies the recursive call. *)
      | MsgContinue s' => fun heq => loop s' (body_evolution_expanded eq_refl heq)
      (* If [body] says we are finished, stop. *)
      | MsgFinished t  => fun _   => t
      end eq_refl).

  (* [loop] could also be defined as a script, as follows. *)

  Goal S -> T.
  Proof.
    eapply (Fix wf_evolution). intros s self.
    destruct (body s) eqn:heq.
    eapply self. eapply body_evolution_expanded. reflexivity. exact heq.
    exact t.
  Defined.

  (* A loop is a fixed point. *)

  (* PUBLIC *)
  Lemma loop_eq:
    forall s,
    loop s =
      match body s as m return (body s = m -> T) with
      | MsgContinue s' => fun heq => loop s'
      | MsgFinished t  => fun _   => t
      end eq_refl.
  Proof.
    intros. unfold loop. rewrite Fix_eq. fold loop. reflexivity.
    (* Now comes the extensionality proof obligation imposed by [Fix_eq]. *)
    { clear s. intros s loop1 loop2 ?.
      (* The following [generalize] is really tricky -- without it, [destruct]
         on the following line is rejected with a cryptic error message. *)
      generalize (@body_evolution_expanded s (body s)). intro.
      destruct (body s); eauto. }
  Qed.

  (* A Hoare-style rule for establishing a loop invariant [I] and its
     consequence [J] after the loop is finished. *)

  (* PUBLIC *)
  Lemma loop_invariant:
    forall (I : S -> Prop) (J : T -> Prop),
    (forall s s', I s -> body s = MsgContinue s' -> I s') ->
    (forall s t , I s -> body s = MsgFinished t  -> J t ) ->
    forall s, I s -> J (loop s).
  Proof.
    intros I J hc hf s. eapply well_founded_ind with (P := fun s => I s -> J (loop s)).
    exact wf_evolution.
    clear s. intros s ih hs.
    rewrite loop_eq.
    destruct (body s) eqn:heq.
    (* Both sub-goals can be proved by [eauto], but I am keeping this for documentation. *)
    { eapply ih.
        eapply body_evolution.
          eapply heq.
        eapply hc.
          eapply hs.
          eapply heq.
    }
    { eapply hf.
        eapply hs.
        eapply heq.
    }
  Qed.

End Loop.

Extraction Inline loop.

(* ---------------------------------------------------------------------------- *)

(* We now instantiate [loop] in the case where the termination proof relies on
   a loop invariant. *)

Section LoopWithInvariant.

  Context { S T : Type }.

  Variable body : S -> message S T.

  Context { evolution : S -> S -> Prop }.

  (* The invariant [I] is a predicate over states. *)

  Context { I : S -> Prop }.

  (* The invariant can be used in the proof of termination. *)

  Hypothesis wf_evolution:
    well_founded (fun s' s => evolution s' s /\ I s /\ I s').

  Hypothesis body_evolution:
    forall s s', I s -> body s = MsgContinue s' -> evolution s' s.

  (* Naturally, the invariant must be preserved by one iteration. *)

  Hypothesis invariant_preserved:
    forall s, I s -> forall s', body s = MsgContinue s' -> I s'.

  (* We instantiate [loop] as follows. *)

  Notation SI := { s : S | I s }.

  (* PRIVATE *)
  Definition body_with_invariant (si : SI) : message SI T :=
    let (s, i) := si in
    match body s as m return (body s = m -> message SI T) with
    | MsgContinue s' => fun heq =>
        MsgContinue (exist _ s' (invariant_preserved i heq))
    | MsgFinished t  => fun  _  =>
        MsgFinished t
    end eq_refl.

  (* PRIVATE *)
  Definition evolution_with_invariant (si' si : SI) :=
    evolution (proj1_sig si') (proj1_sig si).

  (* PRIVATE *)
  Lemma wf_evolution_with_invariant:
    well_founded evolution_with_invariant.
  Proof.
    eapply wf_simulation_functional with (F := @proj1_sig _ I); [ | eapply wf_evolution ].
    intros [ s ? ] [ s' ? ]. unfold evolution_with_invariant. simpl. tauto.
  Qed.

  (* PRIVATE *)
  Ltac destruct_body s :=
    (* There may several proofs of [I s] around, so we must
       use [repeat] here. *)
    repeat match goal with hs: I s |- _ =>
      (* The following [generalize] is really tricky -- without it, [destruct]
         on the following line is rejected with a cryptic error message. *)
      generalize (invariant_preserved hs); intros ?;
      revert hs (* set [hs] aside, to ensure termination *)
    end;
    intros; (* re-introduce the hypotheses that were set aside *)
    destruct (body s) eqn:?; try congruence.

  (* PRIVATE *)
  Lemma body_evolution_with_invariant:
    forall si si',
    body_with_invariant si = MsgContinue si' ->
    evolution_with_invariant si' si.
  Proof.
    unfold body_with_invariant, evolution_with_invariant.
    intros [ s hs ] [ s' hs' ]. simpl.
    destruct_body s. msg_injection.
    eauto using body_evolution.
  Qed.

  (* In the end, we are allowed to construct the loop. This yields a partial
     function, i.e., a function of type [{ s : S | I s } -> T], as opposed
     to [S -> T]. That is, the caller has the obligation to prove that the
     invariant holds initially. *)

  (* PUBLIC *)
  Definition loop_with_invariant : SI -> T :=
    loop body_with_invariant wf_evolution_with_invariant body_evolution_with_invariant.

  (* A loop is a fixed point. This is a re-statement of [loop_eq]. *)

  (* PUBLIC *)
  Lemma loop_eq_with_invariant:
    forall s,
    forall hs : I s,
    loop_with_invariant (exist _ s hs) =
      match body s as m return (body s = m -> T) with
      | MsgContinue s' => fun eq =>
          loop_with_invariant (exist _ s' (invariant_preserved hs eq))
      | MsgFinished t  => fun _  =>
          t
      end eq_refl.
  Proof.
    intros.
    unfold loop_with_invariant. rewrite loop_eq. fold loop_with_invariant.
    unfold body_with_invariant.
    destruct_body s. (* that was quick! *)
  Qed.

  (* The function application [loop_with_invariant (exist _ s hs)] does
     not depend on [hs]. This would be an obvious consequence of proof
     irrelevance, but we go out of our way and prove it without relying
     on this axiom. *)

  (* PUBLIC *)
  Lemma loop_with_invariant_is_proof_irrelevant:
    forall s,
    forall hs1 hs2 : I s,
    loop_with_invariant (exist _ s hs1) = loop_with_invariant (exist _ s hs2).
  Proof.
    (* By well-founded induction on [s]. *)
    intros s. eapply well_founded_ind with (P := fun s => forall hs1 hs2 : I s,
      loop_with_invariant (exist _ s hs1) = loop_with_invariant (exist _ s hs2)
    ). exact wf_evolution.
    clear s. intros s ih hs1 hs2.
    do 2 rewrite loop_eq_with_invariant.
    destruct_body s.
    eapply ih. eauto using body_evolution.
  Qed.

  (* PUBLIC *)
  Lemma loop_with_invariant_is_proof_irrelevant_alt:
    forall s1 s2,
    proj1_sig s1 = proj1_sig s2 ->
    loop_with_invariant s1 = loop_with_invariant s2.
  Proof.
    intros [ s1 hs1 ] [ s2 hs2 ]. simpl. intro; subst.
    eapply loop_with_invariant_is_proof_irrelevant.
  Qed.

  (* A re-statement of [loop_invariant]. This proof rule allows establishing
     an extra invariant [X], in addition to the invariant [I] that was used
     to construct the loop. *)

  (* PUBLIC *)
  Lemma loop_with_invariant_invariant:
    forall (X : S -> Prop) (J : T -> Prop),
    (forall s s', I s -> X s -> body s = MsgContinue s' -> X s') ->
    (forall s t , I s -> X s -> body s = MsgFinished t  -> J t ) ->
    forall s,
    forall hs : I s,
    X s ->
    J (loop_with_invariant (exist _ s hs)).
  Proof.
    intros.
    unfold loop_with_invariant.
    eapply loop_invariant. instantiate (1 := fun s => X (proj1_sig s)).
    { clear dependent s.
      intros [ s hs ] [ s' hs' ]. simpl.
      destruct_body s. msg_injection.
      eauto. }
    { clear dependent s.
      intros [ s hs ] t. simpl.
      destruct_body s. msg_injection.
      eauto. }
    { simpl. eauto. }
  Qed.

  (* PUBLIC *)
  Lemma loop_with_invariant_invariant_alt:
    forall (X : S -> Prop) (J : T -> Prop),
    (forall s s', I s -> X s -> body s = MsgContinue s' -> X s') ->
    (forall s t , I s -> X s -> body s = MsgFinished t  -> J t ) ->
    forall s,
    X (proj1_sig s) ->
    J (loop_with_invariant s).
  Proof.
    intros ? ? ? ? [ s hs ]. simpl.
    eapply loop_with_invariant_invariant; eauto.
  Qed.

End LoopWithInvariant.

Extraction Inline body_with_invariant loop_with_invariant.

(* ---------------------------------------------------------------------------- *)

(* Refinement preserves termination. If one has proved already that
   [loop body2] terminates and if one can prove that [body1] refines
   [body2], then [loop body1] terminates too. Furthermore, [loop body1]
   refines [loop body2]. *)

Section Refinement.

  (* Assume we have two loop bodies, each with its own type of state. *)

  Context { S1 T1 S2 T2 : Type }.
  Variable body1 : S1 -> message S1 T1.
  Variable body2 : S2 -> message S2 T2.

  (* Assume [loop body2] is well-defined, i.e., terminates. *)

  Context { evolution2 : S2 -> S2 -> Prop }.
  Hypothesis wf_evolution2 : well_founded evolution2.
  Hypothesis body2_evolution2:
    forall s s',
    body2 s = MsgContinue s' ->
    evolution2 s' s.

  (* Assume there is a relation [RS] between the two state types.
     Assume this relation is defined everywhere, i.e., every
     concrete state is in relation with some abstract state. *)

  Context { RS : S1 -> S2 -> Prop }.

  Hypothesis definedness:
    forall s1 s1', body1 s1 = MsgContinue s1' -> exists s2, RS s1 s2.

  Context { RT : T1 -> T2 -> Prop }.

  (* Assume [body1] refines [body2], i.e., the execution of the loop
     bodies preserves the relation [R]. *)

  Hypothesis refinement:
    forall s1 s2,
    RS s1 s2 ->
    message_eq RS RT (body1 s1) (body2 s2).

  (* Then, [loop body1] is well-defined, i.e., terminates. *)

  (* PRIVATE *)
  Lemma wf_evolution1 : well_founded (fun s' s => body1 s = MsgContinue s').
  Proof.
    (* Note that we have picked the tighest possible definition of
       [evolution1]. This makes the proof of [body_evolution] trivial.
       There only remains to prove that this relation is well-founded. *)
    eapply wf_simulation with (R := RS); [ | | eapply wf_evolution2 ].
    (* Simulation. *)
    { intros s1 s2 s1' hr h1.
      set (hm := refinement hr).
      rewrite h1 in hm.
      inversion hm as [ ? s'2 hr' | ]; subst; clear hm.
      exists s'2. eauto using body2_evolution2. }
    (* Definedness. *)
    { exact definedness. }
  Qed.

  (* Thus, the refined loop can be constructed as follows. *)

  (* PUBLIC *)
  Definition refine_loop : S1 -> T1 :=
    loop body1
      wf_evolution1
      (fun _ _ h => h). (* trivial proof of [body_evolution] *)

  (* The new loop refines the original loop. *)

  (* PUBLIC *)
  Lemma refine_loop_refines_loop:
    forall s1 s2,
    RS s1 s2 ->
    RT (refine_loop s1) (loop body2 wf_evolution2 body2_evolution2 s2).
  Proof.
    (* By well-founded induction on [s1]. Could be on [s2], too. *)
    intros s1. eapply well_founded_ind with (P := fun s1 => forall s2, RS s1 s2 ->
      RT (refine_loop s1) (loop body2 wf_evolution2 body2_evolution2 s2)
    ). exact wf_evolution1.
    clear s1. intros s1 ih s2 hr.
    (* Unfold the two loop bodies. *)
    unfold refine_loop. do 2 rewrite loop_eq.
    (* Perform case analysis over [body1 s1] and [body2 s2]. This gives
       rise to four cases, two of which are impossible, thanks to the
       [refinement] hypothesis. *)
    destruct (body1 s1) eqn:heq1; destruct (body2 s2) eqn:heq2;
    set (hm := refinement hr);
    rewrite heq1 in hm; rewrite heq2 in hm;
    inversion hm; subst;
    (* Two cases remain. The result is by assumption in case [MsgFinished]
       and by the induction hypothesis in case [MsgContinue]. *)
    eauto.
  Qed.

  (* The combinator [refine_loop] is a special case of [loop], so in
     principle, the lemmas [loop_eq] and [loop_invariant] can be used to
     reason about [refine_loop]. *)

End Refinement.

(* By default, the extracted OCaml code for [refine_loop] has an unused
   parameter [body2], which is unpleasant. This parameter appears because
   [body2] is used in the termination proof; and it is not erased because its
   sort is not [Prop]. In some cases, if we request that [refine_loop] be
   inlined at its use site, then (almost magically) the parameter [body2] is
   instantiated with its actual value at the use site, and vanishes -- of
   course, since it is unused. Nevertheless, it seems preferable to explicitly
   declare that this parameter should never appear. This is done as
   follows. *)

Extraction Implicit refine_loop [ body2 ].

Extraction Inline refine_loop.

