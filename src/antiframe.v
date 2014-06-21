Require Import ssreflect ssrbool ssrfun ssrnat eqtype tuple seq fintype.
Require Import bitsrep procstate procstatemonad SPred septac spec.
Require Import cursor pointsto pfun safe.
Require Import triple (* for toPState *).
Require Import Setoid CSetoid Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
  destruct (s Registers r) as [v|]; intuition.
Qed.

Definition regNotIn r (P: SPred) :=
  forall s, P s -> s Registers r = None.

(*
Conjecture regNotIn_alt: forall r P,
  regNotIn r P <-> 
  P //\\ (r? ** ltrue) |-- lfalse.
*)

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
  |-- (S -->> safe @ P) <@ r? ->
  regNotIn r P ->
  AtContra S ->
  S |-- safe @ P.
Proof.
  Transparent ILPre_Ops PStateSepAlgOps sepILogicOps ILFun_Ops.

  rewrite /stateIsAny.
  rewrite <-spec_reads_ex.
  move => H HPr Hcontra k R HS. move => s Hps.

  lforwardR H.
  { apply lforallL with (s.(registers) r).
    rewrite ->spec_reads_entails_at; last by apply _.
    autorewrite with push_at. reflexivity. }
  apply landAdj in H.
  lforwardL H.
  { apply landR; first apply ltrueR. reflexivity. }

  rewrite ->lentails_eq, ->sepSPA, <-lentails_eq in Hps.

  destruct Hps as [sP [s' [Hsp [HsP Hs']]]].
  edestruct stateSplitsAs_reg_or with (r:=r) as [HrP | Hr_else]; first apply Hsp.
  { exfalso. specialize (HPr sP HsP). rewrite HPr in HrP.
    simpl in HrP. discriminate. }

  specialize (H k (eq_pred (removeRegFromPState s' r))). simpl in H. apply H.
  { assert (regIs r (s.(registers) r) ** eq_pred (removeRegFromPState s' r)
            |-- R ** ltrue) as HRtrue.
    { rewrite ->lentails_eq in Hs'. rewrite <-Hs'. apply stateSplitsAs_eq.
      rewrite <-matchRegInPStateDom_addRegToPState; last eassumption.
      by apply stateSplitsOn. }
    rewrite ->HRtrue. rewrite sepSPC. by apply spec_frame. }
  rewrite ->lentails_eq, ->!sepSPA, <-lentails_eq.
  do 2 eexists. do 2 (split; first eassumption).
  clear - Hr_else.
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
(* TODO: generalize side condition on P: probably P just needs to be
   closed under removal of r. Then if r is in sP, we can move it to the ltrue
   part of the heap. *)
(* TODO: is the theorem strong enough to easily extend to multiple registers? *)