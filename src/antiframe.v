(*===========================================================================
    Anti-frame rule for registers

    This rule allows removing a register from the footprint of a program even
    though the program reads and writes it, as long as the value is restored at
    the end. This captures the common (PUSH r;; c;; POP r) pattern.
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import procstate SPred spec pointsto safe septac.
Require Import triple (* for toPState *).
Require Import Setoid CSetoid Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.

Definition regNotIn (r: AnyReg) (P: SPred) :=
  (P ** ltrue) //\\ (r?  ** ltrue) |-- P ** r? ** ltrue.

Theorem antiframe_register (r: AnyReg) P S:
  regNotIn r P ->
  AtContra S ->
  (forall v, S @ (r~=v) |-- safe @ (P ** r~=v)) ->
  S |-- safe @ P.
Proof.
  move => HPr Hcontra H k R HS. move => s Hps.
  specialize (H (s.(registers) r)).
  rewrite ->lentails_eq, ->sepSPA, <-lentails_eq in Hps.
  destruct Hps as [sP [s' [Hsp [HsP Hs']]]].

  (* Without loss of generality, we can assume that register r is in s' (not
     sP). Otherwise, we can "move" it to s': regNotIn lets us isolate it in sP,
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
      destruct Hsr as [sr' [strue [Hsr [[v Hsr'] _]]]].
      destruct (stateSplitsAsIncludes Hsr) as [Hsr'_sr _].
      simpl in Hsr'. rewrite <- Hsr' in Hsr'_sr.
      erewrite (stateIncludedIn_trans Hsr'_sr Hsr_s''); last by rewrite /= eq_refl.
      erewrite (stateIncludedIn_trans Hsr'_sr Hsr_sP); last by rewrite /= eq_refl.
      done.
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
  regNotIn r P ->
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


(* Now follows lemmas for proving regNotIn. *)

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

Lemma regNotIn_sepSP r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P ** Q).
Proof.
  rewrite /regNotIn => HrNotInP HrNotInQ.
  rewrite ->stateAny_atomic.
  apply lorL; last first.
  - rewrite ![(P ** Q) ** _]sepSPA. cancel2. cancel2. by apply landL2.
  - rewrite ->stateAny_atomic. rewrite lor_sepSP. apply lorL.
    + rewrite -{1}[P]empSPR. rewrite ->(ltrueR empSP).
      rewrite ->HrNotInP. by ssimpl.
    + rewrite -{1}[Q]empSPR. rewrite ->(ltrueR empSP).
      rewrite ->HrNotInQ. by ssimpl.
Qed.
Hint Resolve regNotIn_sepSP : reg_not_in.

Lemma regNotIn_or r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P \\// Q).
Proof.
  rewrite /regNotIn => HrNotInP HrNotInQ. rewrite lor_sepSP.
  apply landAdj; apply lorL; apply limplAdj.
  - rewrite lor_sepSP. by apply lorR1.
  - rewrite lor_sepSP. by apply lorR2.
Qed.
Hint Resolve regNotIn_or : reg_not_in.

Lemma regNotIn_exists r T (P: T -> SPred):
  (forall t, regNotIn r (P t)) -> regNotIn r (lexists P).
Proof.
  rewrite /regNotIn => HrNotInP.
  apply landAdj. sdestruct => t. apply limplAdj. ssplit. apply HrNotInP.
Qed.
Hint Resolve regNotIn_exists : reg_not_in.

Lemma regNotIn_false r:
  regNotIn r lfalse.
Proof.
  rewrite /regNotIn. apply landL1. rewrite ->lfalse_is_exists at 1.
  by sdestruct.
Qed.
Hint Resolve regNotIn_false : reg_not_in.

Lemma regNotIn_true r:
  regNotIn r ltrue.
Proof.
  rewrite /regNotIn. apply landL2. rewrite <-(ltrueR empSP) at 2. by ssimpl.
Qed.
Hint Resolve regNotIn_true : reg_not_in.

(* I have not found modular proofs of regNotIn for lforall, //\\, -* and -->>.
   Proofs exist for lforall and //\\ for a stronger definition: P is closed
   under removal of r from its states. Other proofs might exist for an even
   stronger definition: r is not in any of P's states. But the latter definition
   excludes "ltrue".
 *)

Lemma regNotIn_flag r (f: Flag) (v: FlagVal):
  regNotIn r (f ~= v).
Proof.
  rewrite /regNotIn. rewrite ->stateAny_atomic. apply lorL.
  - move => s [s1 [_ [_ [Hs1 _]]]].
    destruct Hs1 as [Hfv [sr [strue [Hs1 [[vr Hsr] _]]]]].
    move/stateSplitsAsIncludes: Hs1 => [Hs1 _]. simpl in Hfv, Hsr.
    rewrite <-Hfv, <-Hsr in Hs1.
    specialize (Hs1 Registers r vr). rewrite /= eq_refl in Hs1.
    cbv in Hs1. intuition. discriminate.
  - cancel2. by apply landL2.
Qed.
Hint Resolve regNotIn_flag : reg_not_in.

Lemma regNotIn_flagAny r (f: Flag):
  regNotIn r (f?).
Proof.
  apply regNotIn_exists. apply regNotIn_flag.
Qed.
Hint Resolve regNotIn_flagAny : reg_not_in.

Lemma regNotIn_reg (r r': AnyReg) (v: DWORD):
  r != r' -> regNotIn r (r' ~= v).
Proof.
  rewrite /regNotIn => Hrr'. rewrite ->stateAny_atomic. apply lorL.
  - move => s [s1 [_ [_ [Hs1 _]]]].
    destruct Hs1 as [Hfv [sr [strue [Hs1 [[vr Hsr] _]]]]].
    move/stateSplitsAsIncludes: Hs1 => [Hs1 _]. simpl in Hfv, Hsr.
    rewrite <-Hfv, <-Hsr in Hs1.
    specialize (Hs1 Registers r vr). rewrite /= eq_refl in Hs1.
    rewrite ifN_eqC in Hs1; last assumption.
    cbv in Hs1. intuition. discriminate.
  - cancel2. by apply landL2.
Qed.
Hint Resolve regNotIn_reg : reg_not_in.

Lemma regNotIn_regAny r (r': AnyReg):
  r != r' -> regNotIn r (r'?).
Proof.
  move => Hr'. apply regNotIn_exists => v. by apply regNotIn_reg.
Qed.
Hint Resolve regNotIn_regAny : reg_not_in.


(* TODO: extend antiframe to flags *)
(* TODO: regNotIn_pointsto family along with forall, -->>, -*, ->>, /\\ *)
(* TODO: is the theorem strong enough to easily extend to multiple registers? *)
(* TODO: corollary for basic *)
(* TODO: extend to other RHS than [safe @ P]? The only property of [safe] we're
   really using here is that it adds [** ltrue] _and nothing more_ to the frame.
 *)
