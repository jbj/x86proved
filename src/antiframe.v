(*===========================================================================
    Anti-frame rule for registers

    This rule allows removing a register from the footprint of a program even
    though the program reads and writes it, as long as the value is restored at
    the end. This captures the common (PUSH r;; c;; POP r) pattern.
  ===========================================================================*)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import procstate SPred spec pointsto safe.
Require Import triple (* for toPState *).
Require Import Setoid CSetoid Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.

(* P is closed under removal of r. Intuitively, it means that r does not occur
 * in P. *)
Definition regNotIn r (P: SPred) :=
  forall s, P s -> P (removeRegFromPState s r).


Theorem antiframe_register (r: AnyReg) P S:
  regNotIn r P ->
  AtContra S ->
  |-- (S -->> safe @ P) <@ r? ->
  S |-- safe @ P.
Proof.
  rewrite /stateIsAny.
  rewrite <-spec_reads_ex.
  move => HPr Hcontra H k R HS. move => s Hps.

  lforwardR H.
  { apply lforallL with (s.(registers) r).
    rewrite ->spec_reads_entails_at; last by apply _.
    autorewrite with push_at. reflexivity. }
  apply landAdj in H.
  lforwardL H.
  { apply landR; first apply ltrueR. reflexivity. }

  rewrite ->lentails_eq, ->sepSPA, <-lentails_eq in Hps.
  destruct Hps as [sP [s' [Hsp [HsP Hs']]]].

  (* Without loss of generality, we can assume that register r is in s' (not
     sP). Otherwise, we can "move" it to s': it can be removed from sP because
     P is closed under removal of r, and it can be added to s' because the
     ltrue assertion can absorb it. *)
  without loss : sP s' HsP Hsp Hs' / s' Registers r = (toPState s) Registers r.
  { edestruct stateSplitsAs_reg_or with (r:=r) as [HrP | HrQ];
      first apply Hsp; last first.
    { apply; try eassumption. }
    move/(_ (removeRegFromPState sP r) (addRegToPState s' r (s.(registers) r))). apply.
    - by apply HPr.
    - rewrite /removeRegFromPState /restrictState /matchRegInPStateDom.
      move => [] r'; try apply (Hsp _ _); [].
      simpl. case Hr': (r == r') => /=.
      + rewrite -(eqP Hr'). by auto.
      + specialize (Hsp Registers r'). by rewrite /= in Hsp.
    - destruct Hs' as [sR [strue [Hs' [HsR _]]]].
      exists sR. exists (addRegToPState strue r (s.(registers) r)).
      split; last by intuition.
      have Hrs' := stateSplitsAs_Some_None Hsp HrP.
      move => [] r'; try apply (Hs' _ _); [].
      simpl. move/(_ _ r'): Hs'. case Hr': (r == r') => /=.
      + rewrite -(eqP Hr') => Hs'. right.
        destruct (s' Registers r) as [v|]; last tauto. discriminate.
      + specialize (Hsp Registers r'). by rewrite /= in Hsp.
    - by rewrite /= eq_refl.
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


(* Now follows a hint database for proving regNotIn *)

Lemma regNotIn_sepSP r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P ** Q).
Proof.
  move => HrNotInP HrNotInQ s HPQ.
  destruct HPQ as [sP [sQ [Hs [HsP HsQ]]]].
  wlog : P Q sP sQ HrNotInP HrNotInQ Hs HsP HsQ
           / sP Registers r = s Registers r.
  { edestruct stateSplitsAs_reg_or with (r:=r) as [HrP | HrQ]; first apply Hs.
    { apply; eassumption. }
    move/(_ Q P sQ sP) => Hwlog. rewrite ->lentails_eq, sepSPC, <-lentails_eq.
    apply: Hwlog; try done; []. by apply sa_mulC.
  }
  move => HrP.
  exists (removeRegFromPState sP r). exists sQ. split; last first.
  + split; last done. by apply HrNotInP.
  + move => f r'. rewrite /removeRegFromPState /restrictState /matchRegInPStateDom.
    destruct f.
    * case Hrx: (r == r').
      - rewrite -(eqP Hrx). split; first done.
        specialize (Hs Registers r'). rewrite -(eqP Hrx) HrP in Hs.
        destruct (s Registers r); last tauto.
        destruct Hs as [|[_ Hs]]; first tauto. done.
      - apply (Hs Registers).
    * apply (Hs Memory).
    * apply (Hs Flags).
    * apply (Hs Traces).
Qed.
Hint Resolve regNotIn_sepSP : reg_not_in.

Lemma regNotIn_or r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P \\// Q).
Proof.
  move => HrNotInP HrNotInQ s [HP|HQ].
  - left. by apply HrNotInP.
  - right. by apply HrNotInQ.
Qed.
Hint Resolve regNotIn_or : reg_not_in.

Lemma regNotIn_exists r T (P: T -> SPred):
  (forall t, regNotIn r (P t)) -> regNotIn r (lexists P).
Proof.
  move => HrNotInP s [t HP].
  exists t. by apply HrNotInP.
Qed.
Hint Resolve regNotIn_exists : reg_not_in.

Lemma regNotIn_and r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P //\\ Q).
Proof.
  move => HrNotInP HrNotInQ s [HP HQ]. split.
  - by apply HrNotInP.
  - by apply HrNotInQ.
Qed.
Hint Resolve regNotIn_and : reg_not_in.

Lemma regNotIn_false r:
  regNotIn r lfalse.
Proof. done. Qed.
Hint Resolve regNotIn_false : reg_not_in.

Lemma regNotIn_true r:
  regNotIn r ltrue.
Proof. done. Qed.
Hint Resolve regNotIn_true : reg_not_in.

Lemma regNotIn_flag r (f: Flag) (v: FlagVal):
  regNotIn r (f ~= v).
Proof.
  move => s Hs. rewrite /removeRegFromPState /matchRegInPStateDom /restrictState.
  move => frag d. specialize (Hs _ d). destruct frag; try done.
  simpl in *. by destruct (r != d).
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
  move => Hr' s Hs. move => frag d. specialize (Hs _ d). destruct frag; try done.
  simpl in *. rewrite /removeRegFromPState /matchRegInPStateDom /restrictState.
  case Hr'd: (r' == d).
  - rewrite ->(eqP Hr'd) in *. rewrite Hr'. by rewrite eq_refl in Hs.
  - rewrite Hr'd in Hs. by destruct (r != d).
Qed.
Hint Resolve regNotIn_reg : reg_not_in.

Lemma regNotIn_regAny r (r': AnyReg):
  r != r' -> regNotIn r (r'?).
Proof.
  move => Hr'. apply regNotIn_exists => v. by apply regNotIn_reg.
Qed.
Hint Resolve regNotIn_regAny : reg_not_in.


Module SanityChecking_regNotIn.
  Definition regIsNone r (P: SPred) :=
    forall s, P s -> s Registers r = None.

  Lemma reg_IsNone_NotIn r P:
    regIsNone r P -> regNotIn r P.
  Proof.
    rewrite /regIsNone /regNotIn => H s Hs.
    replace (removeRegFromPState s r) with s; first done.
    apply functional_extensionality_dep.
    move => []; try reflexivity.
    apply functional_extensionality => r'.
    rewrite /removeRegFromPState /restrictState /matchRegInPStateDom.
    case Hr': (r == r'); last done. rewrite -(eqP Hr'). by apply H.
  Qed.
End SanityChecking_regNotIn.

(* TODO: extend to flags *)
(* TODO: regNotIn_pointsto family along with forall, -->>, -*, ->>, /\\ *)
(* TODO: is the theorem strong enough to easily extend to multiple registers? *)
(* TODO: corollaries for basic and without <@ *)