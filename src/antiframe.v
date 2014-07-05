(*===========================================================================
    Anti-frame rule for registers

    This rule allows removing a register from the footprint of a program even
    though the program reads and writes it, as long as the value is restored at
    the end. This captures the common (PUSH r;; c;; POP r) pattern.
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import procstate SPred spec pointsto reader safe septac.
Require Import triple (* for toPState *).
Require Import Setoid CSetoid Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.

Definition regNotFree (r: AnyReg) (P: SPred) :=
  (P ** ltrue) //\\ (r?  ** ltrue) |-- P ** r? ** ltrue.

Lemma regAny_sub (r: AnyReg) s:
  (r? ** ltrue) s -> exists v, s Registers r = Some v.
Proof.
  move => [sr [strue [Hs1 [[v Hsr] _]]]].
  move/stateSplitsAsIncludes: Hs1 => [Hs1 _].
  simpl in Hsr. rewrite <-Hsr in Hs1.
  exists v. apply Hs1. by rewrite /= eq_refl.
Qed.

Theorem antiframe_register (r: AnyReg) P S:
  regNotFree r P ->
  AtContra S ->
  (forall v, S @ (r~=v) |-- safe @ (P ** r~=v)) ->
  S |-- safe @ P.
Proof.
  move => HPr Hcontra H k R HS. move => s Hps.
  specialize (H (s.(registers) r)).
  rewrite ->lentails_eq, ->sepSPA, <-lentails_eq in Hps.
  destruct Hps as [sP [s' [Hsp [HsP Hs']]]].

  (* Without loss of generality, we can assume that register r is in s' (not
     sP). Otherwise, we can "move" it to s': regNotFree lets us isolate it in sP,
     and it can be added to s' because the ltrue assertion can absorb it. *)
  without loss : sP s' HsP Hsp Hs' / s' Registers r = (toPState s) Registers r.
  { edestruct stateSplitsAs_reg_or with (r:=r) as [HrP | HrQ];
      first apply Hsp; last first.
    { apply; try eassumption. }
    destruct (HPr sP) as [sP' [sr [HsP_split [HsP' Hsr]]]].
    { split.
      - by rewrite ->lentails_eq, <-(ltrueR empSP), empSPR, <-lentails_eq.
      - exists (addRegToPState emptyPState r (s.(registers) r)).
        exists (removeRegFromPState sP r).
        split; last split.
      - rewrite /removeRegFromPState /restrictState /matchRegInPStateDom.
        move => [] r'; try (destruct (sP _ r'); tauto); [].
        simpl. case Hr': (r == r') => /=.
        + rewrite -(eqP Hr') HrP /=. by left.
        + destruct (sP Registers r'); tauto.
      - exists (s.(registers) r). by rewrite /=.
      - done.
    }
    apply sa_mulC in Hsp.
    destruct (sa_mulA Hsp HsP_split) as [s'' [Hsp' Hs'']].
    move/(_ sP' s''). apply; try assumption.
    - destruct Hs' as [sR [strue [Hs' [HsR _]]]].
      exists sR. apply sa_mulC in Hs''.
      destruct (sa_mulA Hs'' Hs') as [sr' [Hs''_sr Hsr']]. by exists sr'.
    - rewrite <- HrP.
      move/stateSplitsAsIncludes: Hs'' => [_ Hsr_s''].
      move/stateSplitsAsIncludes: HsP_split => [_ Hsr_sP].
      move/regAny_sub: Hsr => [v Hsr].
      move/(_ _ _ _ Hsr): Hsr_s'' => ->.
      move/(_ _ _ _ Hsr): Hsr_sP => ->. done.
  }

  move => HsPr.
  specialize (H k (eq_pred (removeRegFromPState s' r))). simpl in H. apply H.
  { assert (regIs r (s.(registers) r) ** eq_pred (removeRegFromPState s' r)
            |-- R ** ltrue) as HRtrue.
    { rewrite ->lentails_eq in Hs'. rewrite <-Hs'. apply stateSplitsAs_eq.
      erewrite <-matchRegInPStateDom_addRegToPState; last eassumption.
      by apply stateSplitsOn. }
    rewrite ->HRtrue. rewrite sepSPC. by apply spec_frame. }
  rewrite ->lentails_eq, ->!sepSPA, <-lentails_eq.
  do 2 eexists. do 2 (split; first eassumption).
  clear - HsPr.
  exists (addRegToPState emptyPState r (s.(registers) r)).
  exists (removeRegFromPState s' r).
  split.
  - erewrite <-matchRegInPStateDom_addRegToPState; last eassumption.
    by apply stateSplitsOn.
  - split.
    + simpl. reflexivity.
    + do 2 eexists. split; first by apply sa_unitI. simpl. done.
Qed.

(* More concise formulation. Probably not very useful with the tactics in this
   development. *)
Corollary antiframe_register_spec_reads (r: AnyReg) P S:
  regNotFree r P ->
  AtContra S ->
  |-- (S -->> safe @ P) <@ r? ->
  S |-- safe @ P.
Proof.
  rewrite /stateIsAny. rewrite <-spec_reads_ex.
  move => HPr Hcontra H. apply: antiframe_register; first eassumption.
  move => v. lforwardR H.
  { apply lforallL with v. rewrite ->spec_reads_entails_at; last by apply _.
    autorewrite with push_at. reflexivity. }
  by apply limplValid.
Qed.


(* Now follows lemmas for proving regNotFree. *)

Instance regNotFree_lequiv r:
  Proper (lequiv --> Basics.impl) (regNotFree r).
Proof.
  rewrite /regNotFree /Basics.flip. by move => P P' ->.
Qed.

Lemma stateSplitsAs_move_register r v s:
  s Registers r = Some v ->
  stateSplitsAs s (addRegToPState emptyPState r v) (removeRegFromPState s r).
Proof.
  move => Hsr.
  rewrite /removeRegFromPState /restrictState /matchRegInPStateDom.
  move => [] r'; try (destruct (s _ r'); tauto); [].
  simpl. case Hr': (r == r') => /=.
  + rewrite -(eqP Hr') Hsr /=. tauto.
  + destruct (s Registers r'); tauto.
Qed.

(* A predicate, here "r?", is _atomic_ when it cannot be divided across sepSP *)
Lemma stateAny_atomic (r: AnyReg) P Q:
  (P ** Q) //\\ (r? ** ltrue) |--
  (P //\\ (r? ** ltrue)) ** Q \\// P ** (Q //\\ (r? ** ltrue)).
Proof.
  move => s [HPQ Hrtrue].
  destruct HPQ as [sP [sQ [Hs_PQ [HsP HsQ]]]].
  without loss : P Q sP sQ Hs_PQ HsP HsQ / sP Registers r = s Registers r.
  { edestruct stateSplitsAs_reg_or with (r:=r) as [HrP | HrQ];
      first apply Hs_PQ.
    { apply; try eassumption. }
    move/(_ Q P sQ sP). apply sa_mulC in Hs_PQ. move/(_ Hs_PQ HsQ HsP HrQ).
    rewrite ->!lentails_eq. etransitivity; first eassumption. apply lorL.
    - apply lorR2. by rewrite sepSPC.
    - apply lorR1. by rewrite sepSPC.
  }
  move => HrP. left. exists sP, sQ. split; first done. split; last done.
  split; first done. destruct Hrtrue as [sr [strue [Hs_r [[v Hsr] _]]]].
  simpl in Hsr. exists sr. exists (removeRegFromPState sP r).
  split; last first.
  { split; last done. exists v. assumption. }
  rewrite <-Hsr. apply stateSplitsAs_move_register. rewrite HrP.
  move/stateSplitsAsIncludes: Hs_r => [Hs_r _].
  erewrite <- Hs_r; first reflexivity. rewrite <-Hsr. by rewrite /= eq_refl.
Qed.

Lemma regNotFree_sepSP r P Q:
  regNotFree r P -> regNotFree r Q -> regNotFree r (P ** Q).
Proof.
  rewrite /regNotFree => HrNotInP HrNotInQ.
  rewrite ->stateAny_atomic.
  apply lorL; last first.
  - rewrite ![(P ** Q) ** _]sepSPA. cancel2. cancel2. by apply landL2.
  - rewrite ->stateAny_atomic. rewrite lor_sepSP. apply lorL.
    + rewrite -{1}[P]empSPR. rewrite ->(ltrueR empSP).
      rewrite ->HrNotInP. by ssimpl.
    + rewrite -{1}[Q]empSPR. rewrite ->(ltrueR empSP).
      rewrite ->HrNotInQ. by ssimpl.
Qed.
Hint Resolve regNotFree_sepSP : reg_not_in.

Lemma regNotFree_or r P Q:
  regNotFree r P -> regNotFree r Q -> regNotFree r (P \\// Q).
Proof.
  rewrite /regNotFree => HrNotInP HrNotInQ. rewrite lor_sepSP.
  apply landAdj; apply lorL; apply limplAdj.
  - rewrite lor_sepSP. by apply lorR1.
  - rewrite lor_sepSP. by apply lorR2.
Qed.
Hint Resolve regNotFree_or : reg_not_in.

Lemma regNotFree_exists r T (P: T -> SPred):
  (forall t, regNotFree r (P t)) -> regNotFree r (lexists P).
Proof.
  rewrite /regNotFree => HrNotInP.
  apply landAdj. sdestruct => t. apply limplAdj. ssplit. apply HrNotInP.
Qed.
Hint Resolve regNotFree_exists : reg_not_in.

(* This definition is stronger than regNotFree but is often easier to prove.
   It does not hold for P=ltrue. *)
Definition regMissingIn (r: AnyReg) (P: SPred) :=
  P //\\ (r?  ** ltrue) |-- lfalse.

Lemma regMissingIn_regNotFree r P:
  regMissingIn r P -> regNotFree r P.
Proof.
  rewrite /regMissingIn /regNotFree => H.
  rewrite ->stateAny_atomic. rewrite ->H.
  apply lorL; first by ssimpl.
  cancel2. by apply landL2.
Qed.
Hint Immediate regMissingIn_regNotFree : reg_not_in.

(* This morphism is not available for regNotFree, and it makes an important
   difference when dealing for spec_reads, whose definition contains lentails.
 *)
Instance regMissingIn_lentails r:
  Proper (lentails --> Basics.impl) (regMissingIn r).
Proof.
  rewrite /regMissingIn /Basics.flip => P P' HP H. by rewrite ->HP.
Qed.

Instance regMissingIn_lequiv r:
  Proper (lequiv ==> iff) (regMissingIn r).
Proof.
  move => P P' [HP HP']. split.
  - by rewrite ->HP'.
  - by rewrite <-HP.
Qed.

Lemma regMissingIn_empSP r:
  regMissingIn r empSP.
Proof.
  move => s [Hemp Hrtrue]. move/regAny_sub: Hrtrue => [vr Hsr].
  rewrite /empSP /sepLogicOps /SABIOps /= in Hemp. destruct Hemp as [Hs _].
  rewrite <-Hs in Hsr. discriminate.
Qed.
Hint Resolve regMissingIn_empSP : reg_not_in.

Lemma regMissingIn_false r:
  regMissingIn r lfalse.
Proof.
  by apply landL1.
Qed.
Hint Resolve regMissingIn_false : reg_not_in.

Lemma regNotFree_true r:
  regNotFree r ltrue.
Proof.
  rewrite /regNotFree. apply landL2. rewrite <-(ltrueR empSP) at 2. by ssimpl.
Qed.
Hint Resolve regNotFree_true : reg_not_in.

Lemma regNotFree_propand r p P:
  regNotFree r P -> regNotFree r (p /\\ P).
Proof.
  move => H. by apply regNotFree_exists.
Qed.
Hint Resolve regNotFree_propand : reg_not_in.

(* I have not found modular proofs of regNotFree for lforall, //\\, -* and -->>.
   Proofs exist for lforall and //\\ for a stronger definition: P is closed
   under removal of r from its states: [P //\\ (r?  ** ltrue) |-- P ** r?].
 *)

Lemma regMissingIn_sepSP r P Q:
  regMissingIn r P -> regMissingIn r Q -> regMissingIn r (P ** Q).
Proof.
  rewrite /regMissingIn => HP HQ. rewrite ->stateAny_atomic. apply lorL.
  - rewrite ->HP. by ssimpl.
  - rewrite ->HQ. by ssimpl.
Qed.
Hint Resolve regMissingIn_sepSP : reg_not_in.

Lemma regMissingIn_exists r T (P: T -> SPred):
  (forall t, regMissingIn r (P t)) -> regMissingIn r (lexists P).
Proof.
  rewrite /regMissingIn => H. apply landAdj. apply lexistsL => t.
  by apply limplAdj.
Qed.
Hint Resolve regMissingIn_exists : reg_not_in.

Lemma regMissingIn_propand r p P:
  regMissingIn r P -> regMissingIn r (p /\\ P).
Proof.
  move => H. by apply regMissingIn_exists.
Qed.
Hint Resolve regMissingIn_propand : reg_not_in.

Lemma regMissingIn_flag r (f: Flag) (v: FlagVal):
  regMissingIn r (f ~= v).
Proof.
  move => s [Hfv Hrtrue]. move/regAny_sub: Hrtrue => [vr Hsr].
  simpl in Hfv. rewrite <-Hfv in Hsr. discriminate.
Qed.
Hint Resolve regMissingIn_flag : reg_not_in.

Lemma regMissingIn_byte r i v:
  regMissingIn r (byteIs i v).
Proof.
  move => s [Hiv Hrtrue]. move/regAny_sub: Hrtrue => [vr Hsr].
  simpl in Hiv. rewrite <-Hiv in Hsr. discriminate.
Qed.
Hint Resolve regMissingIn_byte : reg_not_in.

Lemma regMissingIn_flagAny r (f: Flag):
  regMissingIn r (f?).
Proof.
  rewrite /stateIsAny. by auto with reg_not_in.
Qed.
Hint Resolve regMissingIn_flagAny : reg_not_in.

Lemma regMissingIn_reg (r r': AnyReg) (v: DWORD):
  r != r' -> regMissingIn r (r' ~= v).
Proof.
  move => Hrr' s [Hfv Hrtrue]. move/regAny_sub: Hrtrue => [vr Hsr].
  simpl in Hfv. rewrite <-Hfv in Hsr. rewrite /addRegToPState in Hsr.
  rewrite ifN_eqC in Hsr; last assumption. discriminate.
Qed.
Hint Resolve regMissingIn_reg : reg_not_in.

(* Needed because the regMissingIn_reg is cost 1 and won't apply after Hint
   Immediate. *)
Lemma regNotFree_reg (r r': AnyReg) (v: DWORD):
  r != r' -> regNotFree r (r' ~= v).
Proof.
  move => H. apply regMissingIn_regNotFree. auto with reg_not_in.
Qed.
Hint Resolve regNotFree_reg : reg_not_in.

Lemma regMissingIn_regAny r (r': AnyReg):
  r != r' -> regMissingIn r (r'?).
Proof.
  move => Hr'. rewrite /stateIsAny. by auto with reg_not_in.
Qed.
Hint Resolve regMissingIn_regAny : reg_not_in.

(* Unfortunately we cannot prove this for general memIs since the memIs
   definition does not limit the SPred predicate in any way. *)
Lemma regMissingIn_reader R {reader: Reader R} r i j (v: R) :
  regMissingIn r (i -- j :-> v).
Proof.
  rewrite readerMemIsSimpl. move: i j. induction reader => i j.
  - rewrite /interpReader. by eauto with reg_not_in.
  - rewrite /interpReader. destruct i; by eauto with reg_not_in.
  - rewrite /interpReader. destruct i; by eauto with reg_not_in.
  - rewrite /interpReader. by eauto with reg_not_in.
Qed.
Hint Resolve regMissingIn_reader : reg_not_in.

(* TODO: prove base cases of regNotFree simpler *)
(* TODO: extend antiframe to flags *)
(* TODO: reg_not_in hints for forall, -->>, -*, ->> *)
(* TODO: is the theorem strong enough to easily extend to multiple registers? *)
(* TODO: corollary for basic *)
(* TODO: extend to other RHS than [safe @ P]? The only property of [safe] we're
   really using here is that it adds [** ltrue] _and nothing more_ to the frame.
 *)
