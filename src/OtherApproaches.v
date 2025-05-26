Set Implicit Arguments.
Require Import Lia.
Require Import Coq.Arith.Wf_nat.                 (* [lt_wf] *)
Require Import Coq.Wellfounded.Inclusion.        (* [wf_incl] *)
Require Import Coq.Wellfounded.Inverse_Image.    (* [wf_inverse_image] *)
Require Import Coq.Arith.PeanoNat.               (* [modulo] *)
Require Import Coq.Arith.Peano_dec.              (* [eq_nat_dec] *)
Require Import Recdef.

(* This demos the use of [Function] instead of the [Loop] library. *)

(* ---------------------------------------------------------------------------- *)

(* Use OCaml integers at extraction time. *)

Require Import ExtrOcamlNatInt.
Extract Inlined Constant Nat.modulo => "(mod)".
Extract Inlined Constant Nat.add => "(+)".

(* ---------------------------------------------------------------------------- *)

(* Demo 1. Euclid's GCD algorithm. *)

Function gcd (a : nat) (b : nat) { wf lt b } : nat :=
  if eq_nat_dec b 0 then
    a
  else
    gcd b (a mod b).
Proof.
  (* 1 *)
  intros a b ? _. eauto using Nat.mod_upper_bound.
  (* 2 *)
  eapply lt_wf.
Qed.

(* The extracted code is good. *)
Extraction gcd.

(* And we get the following proof principles. *)
(*
Check gcd_ind.
Check gcd_rec.
Check gcd_rect.
Check gcd_equation.
*)

(* ---------------------------------------------------------------------------- *)

(* GCD can also be defined using [Program]. *)

Require Coq.Program.Program.

Program Fixpoint GCD (a : nat) (b : nat) { wf lt b } : nat :=
  if eq_nat_dec b 0 then
    a
  else
    GCD b (a mod b).
Next Obligation.
  eauto using Nat.mod_upper_bound.
Qed.

(* The extracted code is kind of OK but not very readable. Some
   wrapping and unwrapping of pairs is taking place. *)
Extract Inductive sigT => "( * )" [ "" ].
Extraction Inline projT1 projT2.
Extraction GCD_func.

Program Fixpoint GCD_alt (ab : nat * nat) { wf (fun (ab ab' : nat * nat) => lt (fst ab) (fst ab')) ab } : nat :=
  let (a, b) := ab in
  if eq_nat_dec b 0 then
    a
  else
    GCD b (a mod b).
Next Obligation.
  unfold Wf.MR.
  eapply wf_inverse_image.
  eapply lt_wf.
Defined.

(* Here, the extracted code is good. *)
Extraction GCD_alt.

(* -------------------------------------------------------------------------- *)

(* GCD can also be defined using [Equations]. *)

From Equations Require Import Equations.

Equations gcd' (a : nat) (b : nat) : nat by wf b lt :=
gcd' a b := if eq_nat_dec b 0 then a else gcd' b (a mod b).
Next Obligation.
  eauto using Nat.mod_upper_bound.
Defined.

(* This alternative syntax can also be used:

Equations gcd' (a : nat) (b : nat) : nat
by wf b lt :=
gcd' a b with eq_nat_dec b 0 => {
gcd' _ _ (left _)  := a;
gcd' _ _ (right _) := gcd' b (a mod b);
}.
 *)

(* Here, the extracted code is OK but not great. The
   extracted function [gcd'] takes a pair [(a, b)].
   The projections make the code difficult to read. *)
Extraction gcd'.

(* Now, let us a prove a property of [gcd'] using [funelim]. *)

Lemma gcd'_correctness {a b} :
  gcd' a b >= 0. (* yes, this is trivial *)
Proof.
  funelim (gcd' a b); lia.
Qed.

(* The tactic [funelim] introduces a use of the axiom of dependent
   functional extensionality. *)

Print Assumptions gcd'_correctness.

(* ---------------------------------------------------------------------------- *)

(* Demo 2. Counting up to 100, two by two. I don't know how to do this using
   [Function]. If one attempts to work directly with inhabitants of a subset
   type, one ends up having to write complicated proof terms, dependent [if]'s,
   etc. *)
