(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred OPred SPredTotal septac spec obs step triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import common_tactics common_definitions.
Require Import Setoid RelationClasses Morphisms.
Require Import Relations.
Require Import instrsyntax.

Module Import instrruleconfig.
  Export ssreflect.

  Export procstate bitsops.
  Export spec SPred OPred basic basicprog.
  Export instr pointsto cursor.
  Export instrsyntax.

  Open Scope instr_scope.
End instrruleconfig.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* TODO: needed now? *)
Lemma TRIPLE_nopost P (c: ST unit) O:
  TRIPLE (P ** ltrue) c O ltrue ->
  forall s: ProcState, (P ** ltrue) (toPState s) ->
    exists s', exists o, c s = (o, Success _ (s', tt)).
Proof.
  move=> HTRIPLE s Hs. move/(_ s Hs): HTRIPLE => [s' [o [Hs' _]]].
  by exists s', o.
Qed.

Section UnfoldSpec.
  Transparent ILPre_Ops.

  Lemma TRIPLE_safe_gen (instr:Instr) P O Q (i j: DWORD) sij:
    eq_pred sij |-- i -- j :-> instr -> 
    forall O',
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr) O
            (Q ** R)) ->
    |> (obs O') @ Q |-- obs (catOP O O') @ (EIP ~= i ** P ** eq_pred sij).
  Proof.
    move => Hsij O' HTRIPLE k R HQ. move=> s Hs.
    destruct k. 

    (* k = 0 *)
    - exists nil. admit. 

    (* k <> 0 *) 

    simpl. (*rewrite /runsFor-/runsFor. *)
    (* TODO: This is clumsy. Make it more like in attic/instrrules.v. *)
    specialize (HQ k). simpl in HQ. admit. (*simpl in HQ.  HQ.  simpl.
    rewrite /=/runsFor/manyStep-/manyStep/oneStep/step. eexists _, _, _, simpl. apply: TRIPLE_nopost. rewrite /doMany-/doMany.
    rewrite assoc. eapply triple_letGetReg.
    - by ssimpl.
    rewrite assoc.
    eapply triple_letReadSep.
    - rewrite ->Hsij. by ssimpl.
    rewrite assoc. eapply triple_seq.
    - eapply triple_setRegSepGen. by ssimpl.
    eapply triple_seq.
    - triple_apply HTRIPLE.
    move=> s Hs.
    edestruct (HQ k) as [f [o Hf]]; first omega.
    - rewrite ->lentails_eq. rewrite ->sepSPA, <-lentails_eq.
      eassumption.
    exists f. exists o. by split.
*)
  Qed.
End UnfoldSpec.

Lemma TRIPLE_safecat instr P Q (i j: DWORD) O O':
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) O (Q ** R)) ->
  |-- (|> (obs O') @ Q -->> obs (catOP O O') @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_safe instr P Q (i j: DWORD) O:
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) empOP (Q ** R)) ->
  |-- (|> obs O @ Q -->> obs O @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. have TS:= TRIPLE_safecat (O:= empOP). 
  eforalls TS. rewrite -> empOPL in TS. by apply TS. done. 
Qed. 

Lemma TRIPLE_basic instr P O Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) O (Q ** R)) ->
  |-- basic P instr O Q.
Proof.
  move=> H. rewrite /basic. specintros => i j O'.
  rewrite ->(spec_later_weaken (obs O' @ (EIP~=j ** Q))).
  apply TRIPLE_safecat => R. triple_apply H.
Qed.

(*---------------------------------------------------------------------------
    Interpretations of MemSpec, RegMem, JmpTgt, used to give address-mod-generic
    presentations of rules
  ---------------------------------------------------------------------------*)

Definition interpMemSpecSrc ms (f: SPred -> DWORD -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some (r, optix)
    then
      if optix is Some(rix,sc)
      then
        Forall pbase ixval addr,
        (f (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval
                                   ** addB (addB pbase offset) (scaleBy sc ixval) :-> addr)
          addr)
      else
        Forall pbase addr,
        f (regToAnyReg r ~= pbase ** addB pbase offset :-> addr)
          addr
   else Forall addr, f (offset :-> addr) addr.

Definition interpJmpTgt (tgt: JmpTgt) (nextInstr: DWORD) (f: SPred -> DWORD -> spec) :=
  match tgt with
  | JmpTgtI t =>
    let: mkTgt offset := t in
    f empSP (addB nextInstr offset)

  | JmpTgtR r =>
    Forall addr,
    f (regToAnyReg r ~= addr) addr

  | JmpTgtM ms =>
    interpMemSpecSrc ms f
  end.

Definition specAtMemSpecDst dword ms (f: (DWORDorBYTE dword -> SPred) -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some(r,ixspec)
    then
      if ixspec is Some(rix,sc)
      then
        Forall pbase ixval,
        f (fun v => addB (addB pbase offset) (scaleBy sc ixval) :-> v)
          @ (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval)

      else
        Forall pbase,
        f (fun v => addB pbase offset :-> v)
          @ (regToAnyReg r ~= pbase)
    else f (fun v => offset :-> v) @ empSP.

(*
Definition lentails1 {T} (f g:T -> SPred):= forall x , f x |-- g x.
Definition lentails2 {T} (f g: (T -> SPred) -> spec) := forall x y, lentails1 x y ->
lentails (f x) (f y).
Global Instance specAtMemSpecDst_entails_m dword :
    Proper (eq --> lentails2 --> lentails) (@specAtMemSpecDst dword).
Proof.
  move => ms1 ms2 msE.
  rewrite /Basics.flip in msE. subst.
  move => f1 f2 fE.
  rewrite /Basics.flip/lentails2 in fE.
  rewrite /specAtMemSpecDst.
  destruct ms1.
  destruct sib.
  destruct p.
  destruct o.
  destruct p.
  specintros => pbase1 ixval1.
  rewrite /lentails1 in fE.
  specsplit.
  autorewrite with push_at.
  sbazooka. ssimpl.
  simpl. specintros.
  autorewrite with push_at. specintros => pbase2 ixval2.
  simpl. g fg.
  move => P P' HP c _ <- Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.
*)

Definition specAtMemSpec dword ms (f: DWORDorBYTE dword -> spec) :=
    let: mkMemSpec optSIB offset := ms in
    if optSIB is Some(r, ixspec)
    then
      if ixspec is Some(rix,sc)
      then
        Forall v pbase ixval,
        f v @ (regToAnyReg r ~= pbase ** regToAnyReg rix ~= ixval
               ** addB (addB pbase offset) (scaleBy sc ixval) :-> v)
      else
        Forall v pbase,
        f v @ (regToAnyReg r ~= pbase ** addB pbase offset :-> v)
    else Forall v, f v @ (offset :-> v).

Definition BYTEregIsAux (r: BYTEReg) (d:DWORD) (b: BYTE) : SPred :=
  match r in BYTEReg return SPred with
  | AL => low 8 d == b /\\ EAX ~= d
  | BL => low 8 d == b /\\ EBX ~= d
  | CL => low 8 d == b /\\ ECX ~= d
  | DL => low 8 d == b /\\ EDX ~= d
  | AH => low 8 (@high 24 8 d) == b /\\ EAX ~= d
  | BH => low 8 (@high 24 8 d) == b /\\ EBX ~= d
  | CH => low 8 (@high 24 8 d) == b /\\ ECX ~= d
  | DH => low 8 (@high 24 8 d) == b /\\ EDX ~= d
  end.

Definition BYTEregIs r b := Exists d, BYTEregIsAux r d b.

Definition DWORDorBYTEregIs d : DWORDorBYTEReg d -> DWORDorBYTE d -> SPred :=
  if d as d return DWORDorBYTEReg d -> DWORDorBYTE d -> SPred
  then fun r v => r ~= v else fun r v => BYTEregIs r v.


Definition specAtRegMemDst d (src: RegMem d) (f: (DWORDorBYTE d -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => DWORDorBYTEregIs r v)

  | RegMemM ms =>
    specAtMemSpecDst ms f
  end.

Definition specAtSrc src (f: DWORD -> spec) : spec :=
  match src with
  | SrcI v =>
    f v

  | SrcR r =>
    Forall v,
    (f v @ (regToAnyReg r ~= v))

  | SrcM ms =>
    @specAtMemSpec true ms f
  end.

Definition specAtDstSrc dword (ds: DstSrc dword) (f: (DWORDorBYTE dword -> SPred) -> DWORDorBYTE dword -> spec) : spec :=
  match ds with
  | DstSrcRR dst src =>
    Forall v,
    f (fun w => DWORDorBYTEregIs dst w) v @ (DWORDorBYTEregIs src v)

  | DstSrcRI dst src =>
    f (fun w => DWORDorBYTEregIs dst w) src

  | DstSrcMI dst src =>
    specAtMemSpecDst dst (fun V => f V src)

  | DstSrcMR dst src =>
    Forall v,
    specAtMemSpecDst dst (fun V => f V v) @ (DWORDorBYTEregIs src v)

  | DstSrcRM dst src =>
    specAtMemSpec src (fun v => f (fun w => DWORDorBYTEregIs dst w) v)
  end.

Notation "OSZCP?" := (OF? ** SF? ** ZF? ** CF? ** PF?).
Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

(** These hints are global *)
(** TODO(t-jagro): Find a better place for this, or, better, generalize [InstrArg] *)
Coercion InstrArg_of_DWORDorBYTEReg d : DWORDorBYTEReg d -> InstrArg := if d as d return DWORDorBYTEReg d -> InstrArg then RegArg else BYTERegArg.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

(** Only things without [_rule]s should go in this database *)
Hint Unfold
  evalInstr
  evalSrc evalDst evalDstR evalDstM evalDstSrc
  (** Perhaps we should have [evalMov_rule] and [evalUnaryOp_rule]? *)
  evalMOV evalUnaryOp evalBinOp
  (** Maybe we should write [_rule]s for [evalShiftOp] and [evalCondition]. *)
  evalShiftOp
  makeBOP makeUOP
  (** Having to unfold [InstrArg_of_DWORDorBYTEReg] is a hack *)
  InstrArg_of_DWORDorBYTEReg
  OSZCP
  natAsDWORD
  (** Maybe we should find a better way to deal with [DWORDRegMemR], [evalShiftCount], [evalRegImm], and [SrcToRegImm] *)
  DWORDRegMemR evalShiftCount evalRegImm SrcToRegImm
  (** Maybe we should find a better way to deal with [evalJmpTgt] and [evalRegMem] *)
  evalJmpTgt evalRegMem
: instrrules_eval.

(** Originally, we had the following in a section:
<<
Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : basicapply.
Hint Rewrite
  addB0 low_catB : basicapply.

Hint Unfold interpJmpTgt : specapply.
>> *)

(** Anything with a rule gets opacified *)
Lemma evalReg_rule (r: Reg) v c O Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) O Q ->
  TRIPLE (r~=v ** S) (bind (evalReg r) c) O Q.
Proof. by apply triple_letGetRegSep. Qed.
Global Opaque evalReg.

(* Is there a  better way of doing this? *)
Lemma triple_preEq (T: eqType) (v w:T) P c O Q :
  TRIPLE (v == w /\\ P) (c w) O Q ->
  TRIPLE (v == w /\\ P) (c v) O Q.
Proof. move => S. apply: triple_pre_exists => H. rewrite -(eqP H) eq_refl in S.
triple_apply S using sbazooka. Qed.

Lemma triple_preEq_and_star (T: eqType) (v w:T) P R c O Q :
  TRIPLE ((v == w /\\ P) ** R) (c w) O Q ->
  TRIPLE ((v == w /\\ P) ** R) (c v) O Q.
Proof.
  move => S. triple_apply (@triple_preEq T v w (P ** R) c O Q) using sbazooka.
  triple_apply S using sbazooka.
Qed.

Lemma evalBYTERegAux_rule (r: BYTEReg) d v c O Q :
  forall S,
  TRIPLE (BYTEregIsAux r d v ** S) (c v) O Q ->
  TRIPLE (BYTEregIsAux r d v ** S) (bind (evalBYTEReg r) c) O Q.
Proof.
  rewrite /evalBYTEReg/BYTEregIsAux.
  move => S T.
  destruct r; triple_apply triple_letGetReg using sbazooka;
  autorewrite with triple;
    by apply triple_preEq_and_star.
Qed.

Lemma evalBYTEReg_rule (r: BYTEReg) v c O Q :
  forall S,
  TRIPLE (BYTEregIs r v ** S) (c v) O Q ->
  TRIPLE (BYTEregIs r v ** S) (bind (evalBYTEReg r) c) O Q.
Proof.
move => S T.
apply triple_pre_existsSep => d.
triple_apply evalBYTERegAux_rule. rewrite /BYTEregIs in T.
triple_apply T using sbazooka.
Qed.
Global Opaque evalBYTEReg.

Lemma evalDWORDorBYTEReg_rule d(r: DWORDorBYTEReg d) v c O Q :
  forall S,
  TRIPLE (DWORDorBYTEregIs r v ** S) (c v) O Q ->
  TRIPLE (DWORDorBYTEregIs r v ** S) (bind (evalDWORDorBYTEReg _ r) c) O Q.
Proof.
destruct d; [apply evalReg_rule | apply evalBYTEReg_rule].
Qed.
Opaque evalDWORDorBYTEReg.

Lemma ASSOC (D: WORD) (b c:BYTE) : (D ## b) ## c = D ## b ## c.
Proof. rewrite /catB. apply val_inj. simpl. by rewrite -catA. Qed.

Lemma LOWLEMMA (D: WORD) (b c:BYTE): low 8 (@high 24 8 (D ## b ## c)) == b.
Proof. by rewrite -ASSOC high_catB low_catB. Qed.

Lemma triple_setBYTERegSep r v w :
  forall S, TRIPLE (BYTEregIs r v ** S) (setBYTERegInProcState r w) empOP (BYTEregIs r w ** S).
Proof.
move => S.
rewrite /BYTEregIsAux/setBYTERegInProcState.
destruct r; apply triple_pre_existsSep => d; apply triple_pre_existsSep => _;
  triple_apply triple_letGetRegSep;
  triple_apply triple_setRegSep using (rewrite /BYTEregIs/BYTEregIsAux;
                                       sbazooka;
                                         by (rewrite low_catB || rewrite LOWLEMMA)).
Qed.
Global Opaque setBYTERegInProcState.

Lemma triple_doSetBYTERegSep r (v w: BYTE) c O Q S :
  TRIPLE (BYTEregIs r w ** S) c O Q ->
  TRIPLE (BYTEregIs r v ** S) (do! setBYTERegInProcState r w; c) O Q.
Proof. apply triple_seq. apply triple_setBYTERegSep. Qed.

Lemma triple_setDWORDorBYTERegSep d (r: DWORDorBYTEReg d) v w :
  forall S, TRIPLE (DWORDorBYTEregIs r v ** S) (setDWORDorBYTERegInProcState _ r w) empOP
                   (DWORDorBYTEregIs r w ** S).
Proof. destruct d; [apply triple_setRegSep | apply triple_setBYTERegSep]. Qed.
Global Opaque setDWORDorBYTERegInProcState.

(** TODO(t-jagro): maybe remove the [doSet] versions? *)
Lemma triple_doSetDWORDorBYTERegSep d (r: DWORDorBYTEReg d) v w c O Q S :
  TRIPLE (DWORDorBYTEregIs r w ** S) c O Q ->
  TRIPLE (DWORDorBYTEregIs r v ** S) (do! setDWORDorBYTERegInProcState _ r w; c) O Q.
Proof. apply triple_seq. triple_apply triple_setDWORDorBYTERegSep. Qed.

Lemma evalMemSpecNone_rule offset c O Q :
  forall S,
  TRIPLE S (c offset) O Q ->
  TRIPLE S (bind (evalMemSpec (mkMemSpec None offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec. triple_apply T. Qed.

Lemma evalMemSpecSomeNone_rule (r:Reg) p offset c O Q :
  forall S,
  TRIPLE (r ~= p ** S) (c (addB p offset)) O Q ->
  TRIPLE (r ~= p ** S) (bind (evalMemSpec (mkMemSpec (Some (r, None)) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply T.
Qed.

Lemma evalMemSpec_rule (r:Reg) (ix:NonSPReg) sc p indexval offset c O Q :
  forall S,
  TRIPLE (r ~= p ** ix ~= indexval ** S) (c (addB (addB p offset) (scaleBy sc indexval))) O Q ->
  TRIPLE (r ~= p ** ix ~= indexval ** S) (bind (evalMemSpec (mkMemSpec (Some(r, Some (ix,sc))) offset)) c) O Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply triple_letGetRegSep; sbazooka.
triple_apply T.
Qed.
Global Opaque evalMemSpec.

Lemma evalPush_rule sp (v w:DWORD) (S:SPred) :
  TRIPLE (ESP~=sp ** (sp -# 4) :-> v ** S)
         (evalPush w) empOP
         (ESP~=sp -# 4 ** (sp -# 4) :-> w ** S).
Proof.
triple_apply triple_letGetRegSep.
triple_apply triple_doSetRegSep.
triple_apply triple_setDWORDSep.
Qed.
Global Opaque evalPush.

Lemma getReg_rule (r:AnyReg) v c O Q :
  forall S,
  TRIPLE (r~=v ** S) (c v) O Q ->
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) O Q.
Proof. by apply triple_letGetRegSep. Qed.
Global Opaque getRegFromProcState.

Lemma triple_pre_introFlags P comp O Q :
  (forall o s z c p, TRIPLE (OSZCP o s z c p ** P) comp O Q) ->
  TRIPLE (OSZCP? ** P) comp O Q.
Proof.
  rewrite /OSZCP /stateIsAny.
  (* TODO: could use an sdestruct tactic for TRIPLE. *)
  move=> H s Hs.
  sdestruct: Hs => fo Hs.
  sdestruct: Hs => fs Hs.
  sdestruct: Hs => fz Hs.
  sdestruct: Hs => fc Hs.
  sdestruct: Hs => fp Hs.
  eapply H; eassumption.
Qed.

Lemma triple_doUpdateZPS P O Q n (v: BITS n) c z p s:
  TRIPLE (ZF ~= (v == #0) ** PF ~= (lsb v) ** SF ~= (msb v) ** P) c O Q ->
  TRIPLE (ZF ~= z ** PF ~= p ** SF ~= s ** P) (do!updateZPS v; c) O Q.
Proof. rewrite /updateZPS. move => H. do 3 triple_apply triple_doSetFlagSep. triple_apply H. Qed.
Global Opaque updateZPS.

Lemma triple_letGetDWORDorBYTESep d (p:PTR) (v:DWORDorBYTE d) c O Q :
  forall S,
  TRIPLE (p:->v ** S) (c v) O Q ->
  TRIPLE (p:->v ** S) (bind (getDWORDorBYTEFromProcState _ p) c) O Q.
Proof. destruct d; [apply triple_letGetSep | apply triple_letGetBYTESep]. Qed.
Global Opaque getDWORDorBYTEFromProcState.

Lemma basicForgetFlags T (MI: MemIs T) P (x:T) O Q o s z c p:
  |-- basic (P ** OSZCP?) x O (Q ** OSZCP o s z c p) ->
  |-- basic P x O Q @ OSZCP?.
Proof. move => H. autorewrite with push_at.
basicapply H. rewrite /OSZCP/stateIsAny. sbazooka.
Qed.

Lemma sbbB_ZC n (r : BITS n) carry (v1 v: BITS n) :
  sbbB false v1 v = (carry, r) ->
   ZF~=(r == #(0)) ** CF~=carry |-- CF~=ltB v1 v ** ZF~=(v1 == v).
Proof. move => E.
  have S0 := subB_eq0 v1 v. rewrite E in S0. rewrite S0.
  have HH := (sbbB_ltB_leB v1 v). rewrite E/fst in HH.
  destruct carry. + rewrite HH. by ssimpl. + rewrite ltBNle HH /negb. by ssimpl.
Qed.

Definition ConditionIs cc cv : SPred :=
  match cc with
  | CC_O => OF ~= cv
  | CC_B => CF ~= cv
  | CC_Z => ZF ~= cv
  | CC_S => SF ~= cv
  | CC_P => PF ~= cv
  | CC_BE => Exists cf zf, cv = cf || zf /\\ CF ~= cf ** ZF ~= zf
  | CC_L => Exists sf f, cv = xorb sf f /\\ SF ~= sf ** OF ~= f
  | CC_LE => Exists sf f zf, cv = (xorb sf f) || zf /\\ SF ~= sf ** OF ~= f ** ZF ~= zf
  end.

Local Ltac triple_op_helper :=
  idtac;
  match goal with
    | [ |- TRIPLE _ (do!updateFlagInProcState ?f ?w; _) _ _ ]                                       => triple_apply triple_doSetFlagSep
    | [ |- TRIPLE _ (do!updateZPS ?v; _) _ _ ]                                                      => triple_apply triple_doUpdateZPS
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]                                        => triple_apply triple_letGetFlagSep
    | _ => progress autorewrite with triple
  end.

Local Ltac triple_op_bazooka_using tac :=
  cbv zeta;
  let H := fresh in
  intro H;
    do ?tac;
    try by triple_apply H.

Local Ltac triple_op_bazooka := triple_op_bazooka_using triple_op_helper.

Lemma triple_letGetCondition cc (v:bool) P O Q c:
  TRIPLE (ConditionIs cc v ** P) (c v) O Q ->
  TRIPLE (ConditionIs cc v ** P) (bind (evalCondition cc) c) O Q.
Proof.
  rewrite /evalCondition/ConditionIs; elim cc;
  triple_op_bazooka_using ltac:(idtac;
                                match goal with
                                  | [ |- TRIPLE (lexists _ ** _) _ _ _ ] => apply triple_pre_existsSep => ?
                                  | [ |- TRIPLE (lpropand _ _ ** _) _ _ _ ] => apply triple_pre_existsSep => ?
                                  | [ H : mkFlag _ = mkFlag _ |- _ ] => (inversion H; try clear H)
                                  | _ => progress subst
                                  | _ => progress triple_op_helper
                                  | [ H : TRIPLE _ _ _ _ |- _ ] => triple_apply H using sbazooka
                                end).
Qed.
Global Opaque evalCondition.
Global Opaque ConditionIs.

Lemma evalArithUnaryOpNoCarry_rule o s z p n f arg c' O Q S
: let result := f arg in
  TRIPLE (OF ~= (msb arg != msb result) ** SF ~= msb result ** ZF ~= (result == #(0)) ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** PF ~= p ** S) (let!res = @evalArithUnaryOpNoCarry n f arg; c' res) O Q.
Proof. rewrite /evalArithUnaryOpNoCarry. triple_op_bazooka. Qed.
Global Opaque evalArithUnaryOpNoCarry.

Lemma evalArithUnaryOp_rule o s z c p n (f : BITS n -> bool * BITS n) arg c' O Q S
: let: (carry, result) := eta_expand (f arg) in
  TRIPLE (OF ~= (msb arg != msb result) ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithUnaryOp n f arg; c' res) O Q.
Proof. rewrite /evalArithUnaryOp. triple_op_bazooka. Qed.
Global Opaque evalArithUnaryOp.

Lemma evalArithOpNoCarry_rule o s z c p n (f : bool -> BITS n -> BITS n -> bool * BITS n) arg1 arg2 c' O Q S
: let: (carry, result) := eta_expand (f false arg1 arg2) in
  TRIPLE (OF ~= computeOverflow arg1 arg2 result ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithOpNoCarry n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalArithOpNoCarry. triple_op_bazooka. Qed.
Global Opaque evalArithOpNoCarry.

(** The operation is unspecified if [CF] is unspecified. *)
Lemma evalArithOp_rule o s z (c : bool) p n (f : bool -> BITS n -> BITS n -> bool * BITS n) arg1 arg2 c' O Q S
: let: (carry, result) := eta_expand (f c arg1 arg2) in
  TRIPLE (OF ~= computeOverflow arg1 arg2 result ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= carry ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalArithOp n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalArithOp. triple_op_bazooka. Qed.
Global Opaque evalArithOp.

Lemma evalLogicalOp_rule o s z c p n (f : BITS n -> BITS n -> BITS n) arg1 arg2 c' O Q S
: let result := f arg1 arg2 in
  TRIPLE (OF ~= false ** SF ~= msb result ** ZF ~= (result == #(0)) ** CF ~= false ** PF ~= lsb result ** S) (c' result) O Q ->
  TRIPLE (OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p ** S) (let!res = @evalLogicalOp n f arg1 arg2; c' res) O Q.
Proof. rewrite /evalLogicalOp. triple_op_bazooka. Qed.
Global Opaque evalLogicalOp.

(** TODO(t-jagro): Find a better place for this opacity control *)
Global Opaque setRegInProcState getDWORDFromProcState updateFlagInProcState forgetFlagInProcState.

Ltac instrrule_triple_bazooka_step tac :=
  idtac;
  let tapply H := triple_apply H using tac in
  match goal with
    | [ |- TRIPLE _ (bind (evalDWORDorBYTEReg ?d ?r) _) _ _ ]                                     => tapply (@evalDWORDorBYTEReg_rule d)
    | [ |- TRIPLE _ (bind (evalReg ?r) _) _ _ ]                                                   => tapply evalReg_rule
    | [ |- TRIPLE _ (bind (evalBYTEReg ?r) _) _ _ ]                                               => tapply evalBYTEReg_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec None ?offset)) _) _ _ ]                         => tapply evalMemSpecNone_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec (Some (?r, None)) ?offset)) _) _ _ ]            => tapply evalMemSpecSomeNone_rule
    | [ |- TRIPLE _ (bind (evalMemSpec (mkMemSpec (Some (?r, Some (?ix, ?sc))) ?offset)) _) _ _ ] => tapply evalMemSpec_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOpNoCarry ?f ?arg) _) _ _ ]                              => tapply evalArithUnaryOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithUnaryOp ?f ?arg) _) _ _ ]                                     => tapply evalArithUnaryOp_rule
    | [ |- TRIPLE _ (bind (evalArithOpNoCarry ?f ?arg1 ?arg2) _) _ _ ]                            => tapply evalArithOpNoCarry_rule
    | [ |- TRIPLE _ (bind (evalArithOp ?f ?arg1 ?arg2) _) _ _ ]                                   => tapply evalArithOp_rule
    | [ |- TRIPLE _ (bind (evalLogicalOp ?f ?arg1 ?arg2) _) _ _ ]                                 => tapply evalLogicalOp_rule
    | [ |- TRIPLE _ (bind (evalCondition ?cc) _) _ _ ]                                            => tapply triple_letGetCondition
    | [ |- TRIPLE _ (do!updateFlagInProcState ?f ?w; _) _ _ ]                                     => tapply triple_doSetFlagSep
    | [ |- TRIPLE _ (do!updateZPS ?v; _) _ _ ]                                                    => tapply triple_doUpdateZPS
    | [ |- TRIPLE _ (do!forgetFlagInProcState ?f; _) _ _ ]                                        => tapply triple_doForgetFlagSep
    | [ |- TRIPLE _ (setDWORDorBYTERegInProcState _ ?d ?p) _ _ ]                                  => tapply triple_setDWORDorBYTERegSep
    | [ |- TRIPLE _ (setDWORDorBYTEInProcState ?p ?w) _ _ ]                                       => tapply triple_setDWORDorBYTESep
    | [ |- TRIPLE _ (setRegInProcState ?d ?p) _ _ ]                                               => tapply triple_setRegSep
    | [ |- TRIPLE _ (retn tt) _ _ ]                                                               => tapply triple_skip
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]                                      => tapply triple_letGetFlagSep
    | [ |- TRIPLE _ (bind (getFlagFromProcState ?f) _) _ _ ]                                      => tapply triple_letGetFlag
    | [ |- TRIPLE _ (bind (getRegFromProcState ?r) _) _ _ ]                                       => tapply triple_letGetRegSep
    | [ |- TRIPLE _ (bind (getDWORDorBYTEFromProcState ?d ?p) _) _ _ ]                            => tapply (@triple_letGetDWORDorBYTESep d)
    | [ |- TRIPLE _ (bind (getDWORDFromProcState ?p) _) _ _ ]                                     => tapply triple_letGetDWORDSep
    | [ |- TRIPLE _ (evalPush ?p) _ _ ]                                                           => tapply evalPush_rule
    | [ |- TRIPLE _ (do! ?f; ?g) _ _ ] => eapply triple_seq; [ by do !instrrule_triple_bazooka_step tac | ]
    | _ => apply TRIPLE_basic => *
    | _ => triple_apply triple_pre_introFlags => *; rewrite /OSZCP
    | _ => progress autorewrite with triple
    | _ => progress autounfold with instrrules_eval
  end.

Ltac instrrule_triple_bazooka tac :=
  (try specintros => *; autorewrite with push_at);
  do !instrrule_triple_bazooka_step tac.

Tactic Notation "instrrule_triple_bazooka" "using" tactic3(tac) := instrrule_triple_bazooka tac.
Tactic Notation "instrrule_triple_bazooka" := instrrule_triple_bazooka using idtac.

Ltac change_stateIs_with_DWORDorBYTEregIs :=
  progress repeat match goal with
                    | [ |- appcontext[stateIs (RegOrFlagR (regToAnyReg ?r))] ] => progress change (stateIs r) with (@DWORDorBYTEregIs true r)
                  end.

(** TODO(t-jagro): Find a way to make this nicer. *)
Ltac do_instrrule_using tac :=
  do ?rewrite /specAtSrc/specAtDstSrc/specAtMemSpec/specAtMemSpecDst/specAtRegMemDst;
  try match goal with
        | [ ds : DstSrc _ |- _ ] => elim ds => ? ?
        | [ src : Src |- _ ] => elim src => ?
        | [ rm : RegMem _ |- _ ] => elim rm => ?
      end;
  do ?[ elim_atomic_in_match' | case/(@id (option _)) | case/(@id (_ * _))
        | (* ensure that the goal is of the form [_ -> _] *) (test progress intros); move => ? ];
  try by tac.
(** Make a [Tactic Notation] so we don't need [ltac:()] *)
Tactic Notation "do_instrrule" tactic3(tac) := do_instrrule_using tac.
Ltac do_instrrule_triple := do_instrrule instrrule_triple_bazooka.

(** Some convenience macros for dealing with basicapply. *)
Hint Unfold
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst
  DWORDRegMemR BYTERegMemR DWORDRegMemM DWORDRegImmI fromSingletonMemSpec
  DWORDorBYTEregIs natAsDWORD BYTEtoDWORD
  makeMOV makeBOP makeUOP
  : instrrules_basicapply.

(** Allow us to unfold with a database inside of a term *)
Class instrrules_unfold_helper {T} (A : T) := do_instrrules_unfold_helper : T.

Hint Extern 0 (instrrules_unfold_helper ?A)
=> let H := fresh in
   (pose A as H);
     do ?(autounfold with basicapply instrrules_basicapply in H);
     let B := (eval unfold H in H) in
     clear H;
       exact B
     : typeclass_instances.
Ltac eval_repeat_autounfold_with_basicapply_instrrules_basicapply_in H :=
  let ret := constr:(_ : instrrules_unfold_helper H) in
  let ret' := (eval cbv zeta in ret) in
  ret'.

Ltac instrrules_unfold H :=
  let T := type_of H in
  let T' := eval_repeat_autounfold_with_basicapply_instrrules_basicapply_in T in
  constr:(H : T').

Hint Rewrite
     addB0 low_catB : instrrules_basicapply.

Ltac instrrules_basicapply R :=
  let R' := instrrules_unfold R in
  basicapply R' using (fun Hlem => autorewrite with basicapply instrrules_basicapply in Hlem).
