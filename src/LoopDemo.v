Set Implicit Arguments.
Require Import Lia.
Require Import Coq.Arith.Wf_nat.                 (* [lt_wf] *)
Require Import Coq.Wellfounded.Inclusion.        (* [wf_incl] *)
Require Import Coq.Wellfounded.Inverse_Image.    (* [wf_inverse_image] *)
Require Import Coq.Arith.PeanoNat.               (* [modulo] *)
Require Import Coq.Arith.Peano_dec.              (* [eq_nat_dec] *)
Require Import loop.Loop.

(* This file contains a few demos of the use of [Loop]. *)

(* ---------------------------------------------------------------------------- *)

(* Use OCaml integers at extraction time. *)

Require Import ExtrOcamlNatInt.
Extract Inlined Constant Nat.modulo => "(mod)".
Extract Inlined Constant Nat.add => "(+)".

(* ---------------------------------------------------------------------------- *)

(* Demo 1. Euclid's GCD algorithm. *)

(* The body of Euclid's loop. *)

Definition gcd_body (ab : nat * nat) :=
  let (a, b) := ab in
  if eq_nat_dec b 0 then
    MsgFinished a
  else
    MsgContinue (b, a mod b).

(* The algorithm terminates because [b], the second component of the
   state, decreases at every iteration. *)

Definition gcd_evolution (s' s : nat * nat) :=
  snd s' < snd s.

Lemma gcd_wf:
  well_founded gcd_evolution.
Proof.
  unfold gcd_evolution. eapply wf_inverse_image. eapply lt_wf.
Qed.

Lemma gcd_body_evolution:
  forall s s',
  gcd_body s = MsgContinue s' ->
  gcd_evolution s' s.
Proof.
  unfold gcd_body. intros [ a b ] [ a' b' ].
  destruct (eq_nat_dec b 0).
  { congruence. }
  { intros h. injection h. clear h. intros. subst. unfold gcd_evolution.
    eauto using Nat.mod_upper_bound. }
Qed.

(* Thus, we are allowed to construct the loop. *)

Definition gcd : nat * nat -> nat :=
  loop gcd_body
    gcd_wf gcd_body_evolution.

(* This code has the desired property. *)

Lemma gcd_eq:
  forall a b,
  gcd (a, b) =
    if eq_nat_dec b 0 then
      a
    else
      gcd (b, a mod b).
Proof.
  intros. unfold gcd, gcd_body. rewrite loop_eq.
  (* The match/match optimisation must be justified by a case analysis. *)
  destruct (eq_nat_dec b 0); eauto.
Qed.

(* The code can be extracted as follows. Inlining [loop] and [gcd_body]
   triggers a match/match optimisation in Coq's extraction engine, and allows
   us to obtain the clean code that we would have written by hand in OCaml.
   Although this code apparently constructs a pair at every iteration, a
   recent OCaml compiler is able to produce machine code that keeps the
   parameters [a] and [b] in two registers. *)

Extraction Inline gcd_body.

Extraction gcd.
(* This should yield the following OCaml code:

let rec gcd = function
| (a, b) -> if (=) b 0 then a else gcd (b, ((mod) a b))

so we have, in OCaml:

# gcd (25, 185);;
- : int = 5
# gcd (42, 735);;
- : int = 21
# gcd (8, 13);;
- : int = 1

*)

(* ---------------------------------------------------------------------------- *)

(* Demo 2. Counting up to 100, two by two, accumulating a list of indices.
   This is a loop whose termination argument relies on an invariant, namely
   the property of being even and less than (or equal to) 100. *)

Require Import List.

(* The type of the current state. *)

Notation state := (nat * list nat)%type.

(* The loop body. *)

Definition MAX := 100.
Definition TWO := 2.

Definition count_body (s : state) :=
  let (n, ns) := s in
  if eq_nat_dec n MAX then
    MsgFinished ns
  else
    MsgContinue (n + TWO, n :: ns).

(* The evolution relation. *)

Definition count_evolution (s' s : state) :=
  let (n , _) := s  in
  let (n', _) := s' in
  n' = n + 2.

(* The invariant. *)

Definition count_invariant (s : state) :=
  let (n , _) := s in
  n = 2 * (n/2) /\ n <= MAX.

(* A technical arithmetic lemma. *)

Lemma plus2_div2:
  forall n,
  (n + 2) / 2 = n/2 + 1.
Proof.
Admitted.

(* We must prove the following facts. *)

Lemma wf_count_evolution:
  well_founded (fun s' s =>
    count_evolution s' s /\ count_invariant s /\ count_invariant s'
  ).
Proof.
  eapply wf_incl; [ |
    eapply wf_inverse_image
      with (f := fun s : state => let (n, _) := s in 50 - n/2);
    eapply lt_wf
  ].
  unfold count_evolution, count_invariant. intros [ n' _ ] [ n _ ] ?.
  repeat match goal with h: _ /\ _ |- _ => destruct h end.
  generalize (plus2_div2 n); intro.
  unfold MAX in *. lia.
Qed.

Lemma count_body_evolution:
  forall s s', count_invariant s -> count_body s = MsgContinue s' -> count_evolution s' s.
Proof.
  unfold count_body, count_evolution, count_invariant.
  intros [ n ? ] [ n' ? ] [ ? ? ].
  destruct (eq_nat_dec n MAX); [ congruence | ].
  intro h. injection h. clear h. intro h.
  unfold TWO in *. lia.
Qed.

(* We isolate the following auxiliary lemma because it is used in the
   statement of [count_eq_simplified] below. *)

Lemma count_invariant_preserved_aux:
  forall n ns, count_invariant (n, ns) -> n <> MAX -> count_invariant (n + 2, n :: ns).
Proof.
  unfold count_invariant. intros ? ? [ ? ? ] ?.
  split.
  { generalize (plus2_div2 n); intro. lia. }
  { unfold MAX in *. lia. }
Qed.

Lemma count_invariant_preserved:
  forall s,
  count_invariant s ->
  forall s',
  count_body s = MsgContinue s' ->
  count_invariant s'.
Proof.
  unfold count_body, count_evolution. intros [ n ns ]. intros.
  destruct (eq_nat_dec n MAX); [ congruence | msg_injection ].
  eauto using count_invariant_preserved_aux.
  (* We use [Defined] as opposed to [Qed] because we need to unfold
     this definition in the proof of [count_eq_simplified]. *)
Defined.

(* Thus, we are allowed to construct the loop. *)

Definition count :=
  loop_with_invariant count_body
    wf_count_evolution count_body_evolution count_invariant_preserved.

(* This code has the desired property. *)

Lemma count_eq:
  forall s,
  forall hs : count_invariant s,
  count (exist _ s hs) =
    match count_body s as m return (count_body s = m -> list nat) with
    | MsgContinue s' => fun eq =>
        count (exist _ s' (count_invariant_preserved _ hs eq))
    | MsgFinished t  => fun _  =>
        t
    end eq_refl.
Proof.
  intros. unfold count. rewrite loop_eq_with_invariant. fold count. reflexivity.
Qed.

(* By inlining [count_body] in the statement of [count_eq] and
   exchanging the two [match] constructs, we obtain the following
   somewhat simplified statement of the fixed point equation. *)

Lemma count_eq_simplified:
  forall n ns,
  forall hs : count_invariant (n, ns),
  count (exist _ (n, ns) hs) =
    match eq_nat_dec n MAX with
    | right hneq =>
        count (exist _ (n + 2, n :: ns) (count_invariant_preserved_aux hs hneq))
    | left  heq  =>
        ns
    end.
Proof.
  intros. rewrite count_eq. unfold count_body.
  (* It is definitely not nice to have to rely on a transparent proof!
     So far, I haven't found a better way. Suggestions are welcome! *)
  unfold count_invariant_preserved.
  generalize (count_invariant_preserved_aux hs). intro cxhs.
  destruct (eq_nat_dec n MAX).
  { reflexivity. }
  { reflexivity. }
Qed.

(* Extraction. *)

(* Unfortunately, there seems to be no generic way of translating
   integer constants to integer constants during extraction. *)
Extract Inlined Constant MAX => "100".
Extract Inlined Constant TWO => "2".

Extraction Inline count_body.

Extraction count.
(* This should yield the following OCaml code:

let rec count = function
| (n, ns) ->
  if (=) n 100 then ns else let s' = (((+) n 2), (n :: ns)) in count s'

so we have, in OCaml:

# count (90, []);;
- : int list = [98; 96; 94; 92; 90]

*)

(* As an example of reasoning a posteriori with an extra invariant,
   we prove that if the loop starts at [MIN], then every element in
   the final list is greater than or equal to [MIN]. (We could also
   prove that all of them are even and less than [MAX].) *)

Definition goal MIN (ms : list nat) :=
  forall m, In m ms -> MIN <= m.

Definition extra_invariant MIN (s : state) :=
  let (n, ns) := s in
  MIN <= n /\ goal MIN ns.

Lemma above_min:
  forall MIN,
  forall s,
  proj1_sig s = (MIN, nil) ->
  goal MIN (count s).
Proof.
  intros ? ? heq. unfold count.
  eapply loop_with_invariant_invariant_alt with (X := extra_invariant MIN);
    unfold count_invariant, extra_invariant, count_body.
  (* The extra invariant is preserved. *)
  { intros [ n ns ] [ n' ns' ] [ ? ? ] [ ? ? ] ?.
    destruct (eq_nat_dec n MAX); [ congruence | msg_injection ].
    intros. subst.
    split.
    { lia. }
    { unfold goal in *. simpl. intros ? [ | ].
      intros. subst n. assumption.
      eauto. }
  }
  (* The extra invariant implies the goal. *)
  { intros [ n ns ] ns' [ ? ? ] [ ? ? ] ?.
    destruct (eq_nat_dec n MAX); [ msg_injection | congruence ].
    assumption. }
  (* The extra invariant holds initially. *)
  { destruct s as [ [ n ns ] hs ]. simpl in *.
    injection heq. clear heq. intros. subst.
    split.
      { eauto. }
      { unfold goal. simpl. tauto. }
  }
Qed.
