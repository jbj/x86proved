(*===========================================================================
  Proof that the linked-list implementation meets its spec
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsrep bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe basic program.
Require Import call instr instrsyntax instrcodec instrrules reader pointsto cursor inlinealloc
               listspec listimp triple.
Require Import macros.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope instr_scope.

Lemma inlineHead_correct (r1 r2: Reg) (i j p e: DWORD) v vs :
  inlineHead_spec r1 r2 i j p e v vs (inlineHead r1 r2).
Proof.
rewrite /inlineHead_spec/inlineHead/listSeg-/listSeg. unfold_program.
rewrite /stateIsAny.
specintros => q old.
specapply MOV_RM0_rule. sbazooka.
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. cancel1. by ssimpl.
Qed.

Lemma inlineTail_correct (r1 r2: Reg) (i j p e: DWORD) v vs :
  inlineTail_spec r1 r2 i j p e v vs (inlineTail r1 r2).
Proof.
rewrite /inlineTail_spec/inlineTail/listSeg-/listSeg. unfold_program.
rewrite /stateIsAny.
specintros => q old. specapply MOV_RM_rule. by ssimpl.
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. cancel1. by sbazooka.
Qed.

Lemma inlineCons_correct (r1 r2: Reg) heapInfo failAddr (i j h t e: DWORD) vs :
  inlineCons_spec r1 r2 heapInfo failAddr i j h t e vs (inlineCons r1 r2 heapInfo failAddr).
Proof.
rewrite /inlineCons_spec/inlineCons/updateCons. unfold_program.
specintros => i1 i2 i3.

specapply inlineAlloc_correct. by ssimpl.

(* Failure case *)
specsplit.
  rewrite <-spec_reads_frame. autorewrite with push_at.
  apply limplValid. apply landL1. cancel1. rewrite /stateIsAny. by sbazooka.

(* Success case *)
specintros => pb.
rewrite (memAnySplitAdd pb (m1:=4)) => //.
rewrite -> addB_addn.
do 2 rewrite -> memAny_entails_pointsToDWORD. specintros => d1 d2.

elim E0:(sbbB false (pb+#8) #8) => [carry0 res0].
assert (H:= subB_equiv_addB_negB (pb+#8) #8).
rewrite E0 addB_negBn /snd in H.
rewrite H in E0. replace (pb +#4 +#4) with (pb +#8) by by rewrite -addB_addn.

specapply SUB_RI_rule. sbazooka.

specapply MOV_M0R_rule. rewrite E0. simpl fst. simpl snd. by sbazooka.

specapply MOV_MR_rule. by ssimpl.

(* Final stuff *)
rewrite <-spec_reads_frame. autorewrite with push_at.
apply limplValid. apply landL2. cancel1.
rewrite /OSZCP/listSeg-/listSeg. rewrite /stateIsAny. sbazooka.
Qed.

Lemma callCons_correct (r1 r2: Reg) heapInfo (i j h t e: DWORD) vs :
  |-- callCons_spec r1 r2 heapInfo i j h t e vs (callCons r1 r2 heapInfo).
Proof.

(* First deal with the calling-convention wrapper *)
rewrite /callCons_spec.
autorewrite with push_at.
etransitivity; [|apply toyfun_mkbody]. specintro => iret.

(* Now unfold the control-flow logic *)
rewrite /callCons/basic. specintros => i1 i2. unfold_program.
specintros => i3 i4 i5 i6 i7 -> -> i8 -> ->.

specapply inlineCons_correct. by ssimpl.

(* Now we deal with failure and success cases *)
specsplit.

(* failure case *)
autorewrite with push_at.

unhideReg EDI => olddi.
(* mov EDI, 0 *)
specapply MOV_RI_rule. sbazooka.

rewrite <- spec_reads_frame. apply: limplAdj. apply: landL2.
autorewrite with push_at. cancel1. ssimpl. apply: lorR1. by rewrite /natAsDWORD.

(* success case *)
autorewrite with push_at.

(* jmp SUCCEED *)
specapply JMP_I_rule. by ssimpl.

(* Final stuff *)
rewrite <-spec_later_weaken.
rewrite <-spec_reads_frame.
apply: limplAdj. autorewrite with push_at.
apply: landL2. cancel1.
rewrite /OSZCP/stateIsAny. sbazooka.
apply: lorR2. sbazooka.
Qed.
