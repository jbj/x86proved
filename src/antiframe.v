Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred septac spec.
Require Import cursor pointsto pfun safe.
Require Import triple (* for toPState *).
Require Import Setoid CSetoid Morphisms.
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma sa_mul_Some_None f (d: fragDom f) (x: fragTgt f) (s1 s2 s: PState):
  sa_mul s1 s2 s -> s1 f d = Some x -> s2 f d = None.
Proof.
  move/(_ f d). destruct (s f d); intuition congruence.
Qed.

Definition matchRegInPStateDom (r: AnyReg) (f: Frag) :=
  match f return fragDom f -> bool with
  | Registers => fun r' => r == r'
  | _ => fun _ => false
  end.

Definition removeRegFromPState (s:PState) (r:AnyReg) : PState :=
  restrictState s (fun f x => ~~ matchRegInPStateDom r x).

Lemma matchRegInPStateDom_addRegToPState (s: PState) r v:
  s Registers r = Some v ->
  restrictState s (matchRegInPStateDom r) === addRegToPState emptyPState r v.
Proof.
  rewrite /restrictState.
  move => H [] x /=; try reflexivity; [].
  case Hrx: (r == x); last done. by rewrite -(eqP Hrx).
Qed.

Lemma stateSplitsAs_reg_or s s1 s2 r:
  stateSplitsAs s s1 s2 ->
  s1 Registers r = s Registers r \/ s2 Registers r = s Registers r.
Proof.
  move => Hs. specialize (Hs Registers r).
  destruct (s Registers r) as [v|]; tauto.
Qed.

(* P is closed under removal of r *)
Definition regNotIn r (P: SPred) :=
  forall s, P s -> P (removeRegFromPState s r).

Lemma regNotIn_sepSP r P Q:
  regNotIn r P -> regNotIn r Q -> regNotIn r (P ** Q).
Proof.
  Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.
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

Instance at_contra_entails (S: spec) `{HContra: AtContra S}:
  Proper (ge ++> lentails --> lentails) S.
Proof.
  Transparent ILPre_Ops.
  move => k k' Hk P P' HP H. rewrite <-Hk.
  specialize (HContra P' P HP).
  specialize (HContra k empSP).
  simpl in HContra. rewrite ->!empSPR in HContra. by auto.
  Opaque ILPre_Ops.
Qed.


Theorem antiframe_register (r: AnyReg) P S:
  regNotIn r P ->
  AtContra S ->
  |-- (S -->> safe @ P) <@ r? ->
  S |-- safe @ P.
Proof.
  Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.

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
      have Hrs' := sa_mul_Some_None Hsp HrP.
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
      rewrite <-matchRegInPStateDom_addRegToPState; last eassumption.
      by apply stateSplitsOn. }
    rewrite ->HRtrue. rewrite sepSPC. by apply spec_frame. }
  rewrite ->lentails_eq, ->!sepSPA, <-lentails_eq.
  do 2 eexists. do 2 (split; first eassumption).
  clear - HsPr.
  exists (addRegToPState emptyPState r (s.(registers) r)).
  exists (removeRegFromPState s' r).
  split.
  - (* TODO: these two lines are copied from above *)
    rewrite <-matchRegInPStateDom_addRegToPState; last eassumption.
    by apply stateSplitsOn.
  - split.
    + simpl. reflexivity.
    + do 2 eexists. split; first by apply sa_unitI. simpl. done.
Qed.

(* TODO: extend to RegOrFlag *)
(* TODO: set up hint database to prove side condition on P *)
(* TODO: is the theorem strong enough to easily extend to multiple registers? *)