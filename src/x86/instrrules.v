Ltac type_of t := type of t (* ssreflect bug workaround *).
(*===========================================================================
    Rules for x86 instructions in terms of [safe]
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype tuple.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import spec SPred septac spec safe triple basic basicprog spectac.
Require Import instr instrcodec eval monad monadinst reader pointsto cursor.
Require Import Setoid RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Relations.
Require Import instrsyntax. 

Local Open Scope instr_scope.

(* TODO: needed now? *)
Lemma TRIPLE_nopost P (c: ST unit):
  TRIPLE (P ** ltrue) c ltrue ->
  forall s: ProcState, (P ** ltrue) (toPState s) ->
    exists s', exists o, c s = (o, Success _ (s', tt)).
Proof.
  move=> HTRIPLE s Hs. move/(_ s Hs): HTRIPLE => [s' [o [Hs' _]]].
  by exists s', o. 
Qed.

Section UnfoldSpec.
  Transparent ILPre_Ops.

  Lemma TRIPLE_safe_gen (instr:Instr) P Q (i j: DWORD) sij:
    eq_pred sij |-- i -- j :-> instr ->
    (forall (R: SPred),
     TRIPLE (EIP ~= j ** P ** eq_pred sij ** R) (evalInstr instr)
            (Q ** R)) ->
    |> safe @ Q |-- safe @ (EIP ~= i ** P ** eq_pred sij).
  Proof.
    move => Hsij HTRIPLE k R HQ. rewrite /spec_fun /= in HQ. move=> s Hs.
    destruct k. (* everything's safe in 0 steps *)
    - exists s. exists nil. reflexivity.
    rewrite /doMany -/doMany.
    (* TODO: This is clumsy. Make it more like in attic/instrrules.v. *)
    move: s Hs. apply: TRIPLE_nopost.
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
  Qed.
End UnfoldSpec.

Lemma TRIPLE_safe instr P Q (i j: DWORD):
  (forall (R: SPred),
   TRIPLE (EIP ~= j ** P ** R) (evalInstr instr) (Q ** R)) ->
  |-- (|> safe @ Q -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> instr).
Proof.
  move=> H. rewrite /spec_reads. specintros => s Hs. autorewrite with push_at.
  rewrite sepSPA. apply limplValid.
  eapply TRIPLE_safe_gen; [eassumption|]. move=> R. triple_apply H.
Qed.

Lemma TRIPLE_basic instr P Q:
  (forall (R: SPred), TRIPLE (P ** R) (evalInstr instr) (Q ** R)) ->
  |-- basic P instr Q.
Proof.
  move=> H. rewrite /basic. specintros => i j.
  rewrite ->(spec_later_weaken (safe @ (EIP~=j ** Q))).
  apply TRIPLE_safe => R. triple_apply H.
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

Definition specAtRegMemDst (src: RegMem true) (f: (DWORD -> SPred) -> spec) :spec  :=
  match src with
  | RegMemR r =>
    f (fun v => regToAnyReg r ~= v) 

  | RegMemM ms =>
    specAtMemSpecDst (dword:=true) ms f
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

(*Canonical Structure BYTEReg_PStateOps : PStateOps := 
  @Build_StateIs BYTEReg BYTE (fun r b => Exists d, BYTEregIsAux r d b).

Canonical Structure DWORDorBYTE_StateIs d : StateIs :=
  @Build_StateIs (DWORDorBYTEReg d) (DWORDorBYTE d)
      (if d as d return DWORDorBYTEReg d -> DWORDorBYTE d -> SPred 
      then fun r v => r ~= v else fun r v => r ~= v).
*)

Definition DWORDorBYTEregIs d : DWORDorBYTEReg d -> DWORDorBYTE d -> SPred :=
  if d as d return DWORDorBYTEReg d -> DWORDorBYTE d -> SPred
  then fun r v => r ~= v else fun r v => BYTEregIs r v.

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

(* We open a section in order to localize the hints *)
Section InstrRules.

Hint Unfold 
  specAtDstSrc specAtSrc specAtRegMemDst specAtMemSpec specAtMemSpecDst mkRegMemR
  DWORDorBYTEregIs
  : basicapply.
Hint Rewrite
  addB0 : basicapply.

(*---------------------------------------------------------------------------
    Helpers for pieces of evaluation (adapted from spechelpers and
    triplehelpers)
  ---------------------------------------------------------------------------*)

Hint Unfold
  evalInstr
  evalArithOp evalArithOpNoCarry evalArithUnaryOp evalArithUnaryOpNoCarry
  evalLogicalOp evalBinOp evalShiftOp evalUnaryOp evalCondition 
  evalMOV evalDst evalSrc : eval.

Definition OSZCP o s z c p := OF ~= o ** SF ~= s ** ZF ~= z ** CF ~= c ** PF ~= p.

Definition OSZCP_Any := OF? ** SF? ** ZF? ** CF? ** PF?.

Lemma evalReg_rule (r: Reg) v c Q : 
  forall S,
  TRIPLE (r~=v ** S) (c v) Q -> 
  TRIPLE (r~=v ** S) (bind (evalReg r) c) Q.
Proof. by apply triple_letGetRegSep. Qed. 

(* Is there a  better way of doing this? *)
Lemma triple_preEq (T: eqType) (v w:T) P c Q :
  TRIPLE (v == w /\\ P) (c w) Q ->
  TRIPLE (v == w /\\ P) (c v) Q.
Proof. move => S. apply triple_pre_exists => EQ. rewrite -(eqP EQ) eq_refl in S. 
triple_apply S; sbazooka. Qed. 

Lemma evalBYTERegAux_rule (r: BYTEReg) d v c Q : 
  forall S,
  TRIPLE (BYTEregIsAux r d v ** S) (c v) Q -> 
  TRIPLE (BYTEregIsAux r d v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
rewrite /evalBYTEReg/BYTEregIsAux.
move => S T. 
destruct r; triple_apply triple_letGetReg; sbazooka.
+ triple_apply (@triple_preEq _ (low 8 d) v (EAX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 d) v (EBX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 d) v (ECX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 d) v (EDX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EAX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EBX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (ECX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
+ triple_apply (@triple_preEq _ (low 8 (@high 24 8 d)) v (EDX~=d ** S)); sbazooka. 
  triple_apply T; sbazooka. 
Qed. 

Lemma evalBYTEReg_rule (r: BYTEReg) v c Q : 
  forall S,
  TRIPLE (BYTEregIs r v ** S) (c v) Q -> 
  TRIPLE (BYTEregIs r v ** S) (bind (evalBYTEReg r) c) Q.
Proof.
move => S T.
apply triple_pre_existsSep => d. 
triple_apply evalBYTERegAux_rule. rewrite /BYTEregIs in T. 
triple_apply T; sbazooka. 
Qed. 

Lemma ASSOC (D: WORD) (b c:BYTE) : (D ## b) ## c = D ## b ## c.
Proof. rewrite /catB. apply val_inj. simpl. by rewrite -catA. Qed. 

Lemma LOWLEMMA (D: WORD) (b c:BYTE): low 8 (@high 24 8 (D ## b ## c)) == b.
Proof. by rewrite -ASSOC high_catB low_catB. Qed. 

Lemma triple_setBYTERegSep r v w :
  forall S, TRIPLE (BYTEregIs r v ** S) (setBYTERegInProcState r w) (BYTEregIs r w ** S).
Proof. 
move => S.
rewrite /BYTEregIsAux/setBYTERegInProcState. 
destruct r; apply triple_pre_existsSep => d; apply triple_pre_existsSep => _;
  triple_apply triple_letGetRegSep; triple_apply triple_setRegSep.
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB. 
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB. 
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB. 
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite low_catB. 
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.  
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.  
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.  
+ rewrite /BYTEregIs/BYTEregIsAux. sbazooka. by rewrite LOWLEMMA.  
Qed.

Lemma evalMemSpecNone_rule (r:Reg) p offset c Q :
  forall S,
  TRIPLE (r ~= p ** S) (c (addB p offset)) Q ->
  TRIPLE (r ~= p ** S) (bind (evalMemSpec (mkMemSpec (Some (r, None)) offset)) c) Q.
Proof. move => S T. rewrite /evalMemSpec.
triple_apply triple_letGetRegSep.
triple_apply T. 
Qed. 

Lemma evalMemSpec_rule (r:Reg) (ix:NonSPReg) sc p indexval offset c Q :
  forall S,
  TRIPLE (r ~= p ** ix ~= indexval ** S) (c (addB (addB p offset) (scaleBy sc indexval))) Q ->
  TRIPLE (r ~= p ** ix ~= indexval ** S) (bind (evalMemSpec (mkMemSpec (Some(r, Some (ix,sc))) offset)) c) Q.
Proof. move => S T. rewrite /evalMemSpec. 
triple_apply triple_letGetRegSep. 
triple_apply triple_letGetRegSep; sbazooka. 
triple_apply T. 
Qed. 

Lemma evalPush_rule sp (v w:DWORD) (S:SPred) :
  TRIPLE (ESP~=sp ** (sp -# 4) :-> v ** S) 
         (evalPush w) 
         (ESP~=sp -# 4 ** (sp -# 4) :-> w ** S).
Proof. rewrite /evalPush. 
triple_apply triple_letGetRegSep. 
triple_apply triple_doSetRegSep. 
triple_apply triple_setDWORDSep.
Qed. 

Lemma getReg_rule (r:AnyReg) v c Q : 
  forall S,
  TRIPLE (r~=v ** S) (c v) Q -> 
  TRIPLE (r~=v ** S) (bind (getRegFromProcState r) c) Q.
Proof. by apply triple_letGetRegSep. Qed. 

Lemma triple_pre_introFlags P comp Q :
  (forall o s z c p, TRIPLE (OSZCP o s z c p ** P) comp Q) ->
  TRIPLE (OSZCP_Any ** P) comp Q.
Proof.
  rewrite /OSZCP_Any /OSZCP /stateIsAny.
  (* TODO: could use an sdestruct tactic for TRIPLE. *)
  move=> H s Hs.
  sdestruct: Hs => fo Hs.
  sdestruct: Hs => fs Hs.
  sdestruct: Hs => fz Hs.
  sdestruct: Hs => fc Hs.
  sdestruct: Hs => fp Hs.
  eapply H; eassumption.
Qed.

Lemma triple_doUpdateZPS S Q n (v: BITS n) c z p s:
  TRIPLE (ZF ~= (v == #0) **
          PF ~= (lsb v) **
          SF ~= (msb v) ** S) c Q ->
  TRIPLE (ZF ~= z ** PF ~= p ** SF ~= s ** S) (do!updateZPS v; c) Q.
Proof.
  move=> H. rewrite /updateZPS. 
  triple_apply triple_doSetFlagSep.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep.
  triple_apply H.
Qed.

(*---------------------------------------------------------------------------
    PUSH instruction
  ---------------------------------------------------------------------------*)

(* Generic push *)
Lemma PUSH_rule src sp (v:DWORD) :
  |-- specAtSrc src (fun w => 
      basic    (ESP ~= sp ** sp-#4 :-> v) (PUSH src) (ESP ~= sp-#4 ** sp-#4 :-> w)).  
Proof.
rewrite /specAtSrc. destruct src.
- apply TRIPLE_basic => R.
  rewrite /evalInstr/evalSrc. 
  triple_apply evalPush_rule. 
- elim: ms => [optSIB offset]. 
  case: optSIB => [[base indexAndScale] |]. 
  case: indexAndScale => [[rix sc] |]. 
  rewrite /specAtMemSpec.
  + specintros => oldv pbase indexval. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalPush_rule. 
  + rewrite /specAtMemSpec. specintros => oldv pbase.
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc.
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalPush_rule.
  + rewrite /specAtMemSpec. specintros => oldv. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    autounfold with eval. rewrite /evalSrc/evalMemSpec. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalPush_rule. 

- specintros => oldv. 
  autorewrite with push_at. 
  apply TRIPLE_basic => R. 
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.
  triple_apply evalPush_rule. 
Qed. 

(* PUSH r *)
Corollary PUSH_R_rule (r:Reg) sp (v w:DWORD) :
  |-- basic (r ~= v ** ESP ~= sp    ** sp-#4 :-> w) 
            (PUSH r)
            (r ~= v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicapply (PUSH_rule r). Qed. 

(* PUSH v *)
Corollary PUSH_I_rule (sp v w:DWORD) :
  |-- basic (ESP ~= sp    ** sp-#4 :-> w) 
            (PUSH v)
            (ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicapply (PUSH_rule v). Qed. 

(* PUSH [r + offset] *)
Corollary PUSH_M_rule (r: Reg) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp-#4 :-> w) 
            (PUSH [r + offset])
            (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicapply (PUSH_rule [r + offset]). Qed.

(* PUSH [r] *)
Corollary PUSH_M0_rule (r: Reg) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp-#4 :-> w) 
            (PUSH [r])
            (r ~= pbase ** pbase :-> v ** ESP ~= sp-#4 ** sp-#4 :-> v).
Proof. basicapply (PUSH_rule [r]). Qed. 

(*---------------------------------------------------------------------------
    POP instruction
  ---------------------------------------------------------------------------*)

(* Generic POP *)
Lemma POP_rule (rm:RegMem true) (sp:BITS 32) (oldv v:DWORD):
  |-- specAtRegMemDst rm (fun V =>
      basic (V oldv ** ESP ~= sp    ** sp:->v) (POP rm)
            (V v    ** ESP ~= sp+#4 ** sp:->v)).
Proof.
  rewrite /specAtRegMemDst. destruct rm.
  + apply TRIPLE_basic => R.
    rewrite /evalInstr /evalDst /evalDstR.
    triple_apply evalReg_rule.
    triple_apply evalReg_rule.
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_doSetRegSep. 
    triple_apply triple_setRegSep. 
  + rewrite /specAtMemSpecDst. 
    elim: ms => [optSIB offset]. 
    elim: optSIB => [[base indexAndScale] |]. 
    case: indexAndScale => [[rix sc] |]. 
    - specintros => pbase indexval. 
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.  
      triple_apply evalReg_rule. 
      triple_apply evalMemSpec_rule. 
      triple_apply triple_letGetDWORDSep. 
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep. 
      triple_apply triple_setRegSep. 
    - specintros => pbase. 
      autorewrite with push_at. apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.  
      triple_apply evalReg_rule. 
      triple_apply evalMemSpecNone_rule.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep. 
      triple_apply triple_setRegSep. 
    - autorewrite with push_at. 
      apply TRIPLE_basic => R.
      rewrite /evalInstr/evalDst/evalDstM.  
      triple_apply evalReg_rule. 
      rewrite /evalMemSpec.  
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_letGetDWORDSep.
      triple_apply triple_doSetDWORDSep. 
      triple_apply triple_setRegSep. 
Qed.

(* POP r *)
Corollary POP_R_rule (r:Reg) (sp:BITS 32) (v w:DWORD):
  |-- basic (r ~= v ** ESP ~= sp    ** sp:->w) (POP (RegMemR true r))
            (r ~= w ** ESP ~= sp+#4 ** sp:->w).
Proof. basicapply (POP_rule (RegMemR true r)). Qed. 

(* POP [r + offset] *)
Corollary POP_M_rule (r: Reg) (offset:nat) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** ESP ~= sp    ** sp :-> w) 
            (POP (RegMemM _ [r + offset]))
            (r ~= pbase ** pbase +# offset :-> w ** ESP ~= sp+#4 ** sp :-> w).
Proof. basicapply (POP_rule (RegMemM _ [r + offset])). Qed. 

(* POP [r] *)
Corollary POP_M0_rule (r: Reg) (sp v w pbase:DWORD) :
  |-- basic (r ~= pbase ** pbase :-> v ** ESP ~= sp    ** sp :-> w) 
            (POP (RegMemM _ [r]))
            (r ~= pbase ** pbase :-> w ** ESP ~= sp+#4 ** sp :-> w).
Proof. basicapply POP_M_rule. Qed.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)

(* Generic rule *)
Lemma MOV_rule ds oldv:
  |-- specAtDstSrc ds (fun V v =>
      basic (V oldv) (MOVOP true ds) (V v)).
Proof.
rewrite /specAtDstSrc/DWORDorBYTEregIs.
destruct ds.

+ specintros => v. autorewrite with push_at. apply TRIPLE_basic => R.
  rewrite /evalInstr/evalMOV.  
  triple_apply evalReg_rule. 
  triple_apply triple_setRegSep. 

+ rewrite /specAtMemSpec.
  elim: src => [optSIB offset].     
  case: optSIB => [[base indexopt] |].
  case: indexopt => [[ixreg sc] |]. 
  - specintros => v pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_setRegSep.
  - specintros => v pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.     
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_setRegSep.
  - specintros => v. autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV/evalMemSpec.     
    triple_apply triple_letGetDWORDSep.
    triple_apply triple_setRegSep.

+ rewrite /specAtMemSpecDst.
  specintros => v. 
  elim: dst => [optSIB offset].
  elim: optSIB => [[base indexopt] |]. 
  case: indexopt => [[ixreg sc] |]. 
  - autorewrite with push_at. specintros => pbase ixval. 
    autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.
    triple_apply evalReg_rule. 
    triple_apply evalMemSpec_rule. 
    triple_apply triple_setDWORDSep.
  - specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.     
    triple_apply evalReg_rule. 
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_setDWORDSep.
  - autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV/evalMemSpec/evalDWORDorBYTEReg. 
    triple_apply evalReg_rule. 
    triple_apply triple_setDWORDSep.
   
+ apply TRIPLE_basic => R. 
  rewrite /evalInstr/evalMOV.
  triple_apply triple_setRegSep.

+ rewrite /specAtMemSpecDst. 
  elim: dst => [optSIB offset].
  elim: optSIB => [[base indexopt] |]. 
  case: indexopt => [[ixreg sc] |]. 
  - specintros => pbase ixval. 
    autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_setDWORDSep.
  - specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV.     
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_setDWORDSep.
  - autorewrite with push_at. apply TRIPLE_basic => R. 
    rewrite /evalInstr/evalMOV/evalMemSpec.     
    triple_apply triple_setDWORDSep.
Qed. 

(* Register to register *)
Lemma MOV_RR_rule (r1 r2:Reg) v:
  |-- basic (r1? ** r2 ~= v) (MOV r1, r2) (r1 ~= v ** r2 ~= v).
Proof. rewrite /stateIsAny. specintro => oldv. basicapply (MOV_rule (DstSrcRR true r1 r2)). Qed.

(* Immediate to register *)
Lemma MOV_RI_rule (r:Reg) (v:DWORD) :
  |-- basic (r?) (MOV r, v) (r ~= v).
Proof. rewrite /stateIsAny. specintro => oldv. basicapply (MOV_rule (DstSrcRI true r v)). Qed. 

(* Register to memory *)
Lemma MOV_MR_rule (p: DWORD) (r1 r2: Reg) offset (v1 v2:DWORD) :
  |-- basic (r1~=p ** p +# offset :-> v1 ** r2~=v2)
            (MOV [r1 + offset], r2)
            (r1~=p ** p +# offset :-> v2 ** r2~=v2).
Proof. basicapply (MOV_rule (DstSrcMR true (mkMemSpec (Some (r1, None)) #offset) r2) v1). Qed.

Lemma MOV_MbR_rule (p: DWORD) (r1:Reg) (r2: BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV [r1 + offset], r2)
            (r1 ~= p ** p +# offset :-> v2 ** BYTEregIs r2 v2).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  rewrite /evalDWORDorBYTEReg/evalMemSpec. 
  triple_apply evalBYTEReg_rule. 
  triple_apply evalReg_rule. 
  triple_apply triple_setBYTESep.  
Qed.


Lemma MOV_MbR_ruleGen d (p: DWORD) (r1:Reg) (r2: DWORDorBYTEReg d) offset (v1 v2:DWORDorBYTE d):
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** DWORDorBYTEregIs r2 v2)
            (MOVOP d (DstSrcMR d (mkMemSpec (Some(r1,None)) #offset) r2))
            (r1 ~= p ** p +# offset :-> v2 ** DWORDorBYTEregIs r2 v2).
Proof.
  destruct d. 
  apply MOV_MR_rule.
  apply MOV_MbR_rule.  
Qed. 

Lemma MOV_RMb_rule (p: DWORD) (r1:Reg) (r2:BYTEReg) offset (v1:BYTE) (v2:BYTE) :
  |-- basic (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v2)
            (MOV r2, [r1 + offset])
            (r1 ~= p ** p +# offset :-> v1 ** BYTEregIs r2 v1).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_letGetBYTESep.
  triple_apply triple_setBYTERegSep.
Qed. 

Lemma MOV_MbI_rule (pd:BITS 32) (r1:Reg) offset (v1 v2:BYTE) :
  |-- basic (r1 ~= pd ** pd +# offset :-> v1)
            (MOV BYTE [r1 + offset], v2)
            (r1 ~= pd ** pd +# offset :-> v2).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalMemSpec.
  triple_apply evalReg_rule. 
  triple_apply triple_setBYTESep.
Qed.

(* Immediate to memory *)
Lemma MOV_MI_rule dword (pd:BITS 32) (r:Reg) offset (v w:DWORDorBYTE dword) :
  |-- basic (r ~= pd ** pd +# offset :-> v)
            (MOVOP _ (DstSrcMI dword (mkMemSpec (Some(r, None)) #offset) w))
            (r ~= pd ** pd +# offset :-> w).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalMemSpec. 
  triple_apply evalReg_rule. 
  triple_apply triple_setDWORDorBYTESep.  
Qed.

(* Memory to register *)
Lemma MOV_RM_rule (pd:BITS 32) (r1 r2:Reg) offset (v: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd +# offset :-> v)
            (MOV r1, [r2 + offset])
            (r1 ~= v ** r2 ~= pd ** pd +# offset :-> v).
Proof.
  rewrite /stateIsAny. specintro => v0.
  basicapply (MOV_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))). 
Qed. 

Lemma MOV_RM0_rule (pd:BITS 32) (r1 r2:Reg) (v: DWORD) :
  |-- basic (r1? ** r2 ~= pd ** pd :-> v)
            (MOV r1, [r2])
            (r1 ~= v ** r2 ~= pd ** pd :-> v).
Proof. basicapply MOV_RM_rule. Qed. 

Lemma MOV_M0R_rule (pd:BITS 32) (r1 r2:Reg) (v1 v2: DWORD) :
  |-- basic (r1 ~= pd ** pd :-> v1 ** r2 ~= v2)
            (MOV [r1], r2)
            (r1 ~= pd ** pd :-> v2 ** r2 ~= v2).
Proof. basicapply MOV_MR_rule. Qed. 

(*---------------------------------------------------------------------------
    LEA instruction
  ---------------------------------------------------------------------------*)

Lemma LEA_ruleSameBase (v indexval offset: DWORD) (r: Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r, Some(r1, sc))) offset)))
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r1 ~= indexval).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  triple_apply evalMemSpec_rule.
  triple_apply triple_setRegSep. 
Qed. 

Lemma LEA_rule (old v indexval offset: DWORD) (r r': Reg) (r1:NonSPReg) sc :
  |-- basic (r ~= old ** r' ~= v ** r1 ~= indexval)
            (instr.LEA r (RegMemM _ (mkMemSpec (Some(r', Some(r1, sc))) offset)))
            (r ~= addB (addB v offset) (scaleBy sc indexval) ** r' ~= v ** r1 ~= indexval).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  triple_apply evalMemSpec_rule.
  triple_apply triple_setRegSep. 
Qed. 

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)

(* Generic increment/decrement rule *)
Lemma INCDEC_rule (dir: bool) (src:RegMem true) (oldv:DWORD) o s z c pf:
  |-- specAtRegMemDst src (fun V => 
      basic (V oldv ** OSZCP o s z c pf) (if dir then UOP _ OP_INC src else UOP _ OP_DEC src) 
      (let w := if dir then incB oldv else decB oldv in 
      V w ** OSZCP (msb oldv!=msb w) (msb w) (w == #0) c (lsb w))).
Proof. 
rewrite /specAtRegMemDst.
destruct src. 
  apply TRIPLE_basic => R.
  autounfold with eval. rewrite /evalDst/evalDstR.
  destruct dir;
    triple_apply evalReg_rule; rewrite /evalUnaryOp/OSZCP/evalArithUnaryOpNoCarry;
    triple_apply triple_doSetFlagSep;
    triple_apply triple_doUpdateZPS;
    triple_apply triple_setRegSep.

destruct ms.
+ elim sib => [[r indexAndScale] |]. 
  destruct indexAndScale. destruct p as [rix sc]. rewrite /specAtMemSpecDst. 
  specintros => pbase ixval.
  autorewrite with push_at. 
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM.
  destruct dir. 
  - autounfold with eval. 
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.
  - triple_apply evalMemSpec_rule.
    triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry. 
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.

rewrite /specAtMemSpecDst. 
specintros => pbase.
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM.
    rewrite /evalSrc.
  destruct dir. 
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry. 
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.
  - triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry. 
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.

rewrite /specAtMemSpecDst. 
autorewrite with push_at.  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstM/evalMemSpec.
    rewrite /evalSrc.
  destruct dir. 
  - triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry. 
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.
  - triple_apply triple_letGetDWORDSep. rewrite /evalUnaryOp/evalArithUnaryOp/OSZCP.
    rewrite /evalArithUnaryOpNoCarry. 
    triple_apply triple_doSetFlagSep. rewrite /updateZPS.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_setDWORDSep.
Qed. 

Definition INC_rule := Eval hnf in INCDEC_rule true.
Definition DEC_rule := Eval hnf in INCDEC_rule false.

(* Special case for increment register *)
Corollary INC_R_rule (r:Reg) (v:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (INC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicapply (INC_rule (RegMemR true r)). Qed. 

Corollary INC_M_rule (r:Reg) (offset:nat) (v pbase:DWORD) o s z c pf:
  let w := incB v in
  |-- basic (r ~= pbase ** pbase +# offset :-> v ** OSZCP o s z c pf) (INC [r + offset])
            (r ~= pbase ** pbase +# offset :-> w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicapply (INC_rule (RegMemM _ (mkMemSpec (Some(r, None)) #offset))). Qed. 

Lemma basicForgetFlags T (MI: MemIs T) P (x:T) Q o s z c p:
  |-- basic (P ** OSZCP_Any) x (Q ** OSZCP o s z c p) ->
  |-- basic P x Q @ OSZCP_Any.
Proof. move => H. autorewrite with push_at. 
basicapply H. rewrite /OSZCP/OSZCP_Any/stateIsAny. sbazooka. 
Qed. 

Lemma INC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (INC r) (r~=incB v) @ OSZCP_Any.
Proof.
autorewrite with push_at. rewrite {1}/OSZCP_Any/stateIsAny. specintros => o s z c p. 
basicapply (INC_rule (RegMemR true r)); rewrite /OSZCP/OSZCP_Any/stateIsAny; sbazooka. 
Qed.

(* Special case for decrement *)
Lemma DEC_R_rule (r:Reg) (v:DWORD) o s z c pf :
  let w := decB v in
  |-- basic (r~=v ** OSZCP o s z c pf) (DEC r)
            (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) c (lsb w)).
Proof. basicapply (DEC_rule (RegMemR true r)). Qed. 

Lemma DEC_R_ruleNoFlags (r:Reg) (v:DWORD):
  |-- basic (r~=v) (DEC r) (r~=decB v) @ OSZCP_Any.
Proof. 
autorewrite with push_at. rewrite {1}/OSZCP_Any/stateIsAny. specintros => o s z c p. 
basicapply (DEC_rule (RegMemR true r)); rewrite /OSZCP/OSZCP_Any/stateIsAny; sbazooka. 
Qed. 


Lemma NOT_rule (src:RegMem true) (v:DWORD):
  |-- specAtRegMemDst src (fun V => basic (V v) (UOP true OP_NOT src) (V (invB v))).
Proof. 
rewrite /specAtRegMemDst.
destruct src. 
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  triple_apply evalReg_rule.
  triple_apply triple_setRegSep.

rewrite /specAtMemSpecDst.
destruct ms. 
case sib => [[r indexAndScale] |].
destruct indexAndScale. 
destruct p as [rix sc].
specintros => pbase ixval.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval.
  rewrite /evalDst/evalDstM/evalInstr/evalUnaryOp.
  triple_apply evalMemSpec_rule.
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_setDWORDSep.

specintros => pbase.
autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval. 
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp.
  triple_apply evalMemSpecNone_rule.
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_setDWORDSep.

autorewrite with push_at. apply TRIPLE_basic => R.
  autounfold with eval. 
  rewrite /evalDst/evalDstM/evalSrc/evalUnaryOp. rewrite /evalMemSpec. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_setDWORDSep.
Qed.   

(* Special case for not *)
Lemma NOT_R_rule (r:Reg) (v:DWORD):
  |-- basic (r~=v) (NOT r) (r~=invB v).
Proof. basicapply (NOT_rule (RegMemR true r)). Qed. 

Corollary NOT_M_rule (r:Reg) (offset:nat) (v pbase:DWORD):
  |-- basic (r~=pbase ** pbase +# offset :-> v) (NOT [r + offset])
            (r~=pbase ** pbase +# offset :-> invB v).
Proof. basicapply (NOT_rule (RegMemM true (mkMemSpec (Some(r, None)) #offset))). Qed. 

(* Special case for negation *)
Lemma NEG_R_rule (r:Reg) (v:DWORD) :
  let w := negB v in
  |-- basic
    (r~=v ** OSZCP_Any) (NEG r)
    (r~=w ** OSZCP (msb v!=msb w) (msb w) (w == #0) (v != #0) (lsb w)).
Proof. 
  move => w. apply TRIPLE_basic => R. repeat autounfold with eval.
  rewrite /evalDst/evalDstR.
  triple_apply evalReg_rule.
  assert (HH := subB_equiv_addB_negB #0 v). rewrite /subB in HH. 
  assert (CARRY := sbb0B_carry v).
  case E: (sbbB false #0 v) => [carry res].
  rewrite E in HH. rewrite E in CARRY. simpl snd in HH. simpl fst in CARRY.
  rewrite add0B in HH. rewrite HH. 
  rewrite CARRY.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. rewrite /w. 
  triple_apply triple_setRegSep.
Qed. 

(*---------------------------------------------------------------------------
    ADD instruction
  ---------------------------------------------------------------------------*)
(* Generic ADD *)
Lemma ADD_rule (ds:DstSrc true) (v1: DWORD) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP_Any)
             (BOP true OP_ADD ds)
             (let: (carry,v) := splitmsb (adcB false v1 v2) in
              D v ** OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v))).
Proof.
  rewrite /specAtDstSrc/DWORDorBYTEregIs. 
  destruct ds. 
  (* RR *)
  specintros => v2. 
  autorewrite with push_at. apply TRIPLE_basic => R.
  repeat (autounfold with eval). 
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule. 
  elim: (splitmsb (adcB false v1 v2)) => [carry v]. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
  (* RM *)
  rewrite /specAtMemSpec. 
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + specintros => v2 pbase ixval. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    triple_apply evalReg_rule. 
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. 
  elim: (splitmsb (adcB false v1 v2)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 
(* Non-indexed *)
  + specintros => v2 pbase. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    rewrite /evalDstSrc/evalDstR. 
    triple_apply evalReg_rule.
    triple_apply evalMemSpecNone_rule.    
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDSep. 
    elim: (splitmsb (adcB false v1 v2)) => [carry v].    
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 
(* offset only *)
  + specintro => v2. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    rewrite /evalDstSrc/evalDstR/evalMemSpec. 
    triple_apply evalReg_rule.  
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    elim: (splitmsb (adcB false v1 v2)) => [carry v].    
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 

  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst. 
  elim:dst => [optSIB offset].
  case: optSIB => [[base ixopt] |].  
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule.
    elim: (splitmsb (adcB false v1 v2)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule. 
  elim: (splitmsb (adcB false v1 v2)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule. 
  elim: (splitmsb (adcB false v1 v2)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
  (* RI *)
  apply TRIPLE_basic => R.
  repeat (autounfold with eval).  rewrite /evalDstSrc/evalDstR. 
  triple_apply evalReg_rule. 
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
  elim: (splitmsb (adcB false v1 c)) => [carry v]. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep.  

  (* MI *)
  rewrite /specAtMemSpecDst. 
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |]. 

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep.    
    elim: (splitmsb (adcB false v1 c)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM. 
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_letGetDWORDSep. 
  elim: (splitmsb (adcB false v1 c)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec. 
    triple_apply triple_letGetDWORDSep. 
  elim: (splitmsb (adcB false v1 c)) => [carry v]. 
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
Qed.   

(* ADD r, v2 *)
Corollary ADD_RI_rule (r:Reg) v1 (v2:DWORD):
  |-- basic (r~=v1 ** OSZCP_Any) (ADD r, v2)
            (let: (carry,v) := splitmsb (adcB false v1 v2) in
             r~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. apply (ADD_rule (DstSrcRI true r v2)). Qed.   

Corollary ADD_RI_ruleNoFlags (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1) (ADD r1, v2) (r1~=addB v1 v2) @ OSZCP_Any.
Proof. apply: basicForgetFlags; apply ADD_RI_rule. Qed.

(* ADD r1, r2 *)
Corollary ADD_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP_Any) (ADD r1, r2)
            (let: (carry,v) := splitmsb (adcB false v1 v2) in
             r1~=v ** r2~=v2 ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof. basicapply (ADD_rule (DstSrcRR true r1 r2)). 
elim: (splitmsb _) => [carry v]. sbazooka. Qed. 

Corollary ADD_RR_ruleNoFlags (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP_Any) (ADD r1, r2)
            (r1~=addB v1 v2 ** r2~=v2 ** OSZCP_Any). 
Proof.
rewrite /addB/dropmsb. 
basicapply (ADD_rule (DstSrcRR true r1 r2)). 
elim: (splitmsb _) => [carry v]. 
rewrite /OSZCP_Any/OSZCP/stateIsAny. simpl snd.  
sbazooka. 
Qed. 

Corollary ADD_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (ADD r1, [r2 + offset])
            (let: (carry,v) := splitmsb (adcB false v1 v2) in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  basicapply (ADD_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))). 
elim: (splitmsb _) => [carry v].
sbazooka.
Qed.   

Lemma BINOP_RM_rule (pd:BITS 32) (r1 r2:Reg) (v1 v2:DWORD) (offset:nat):
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (ADD r1, [r2 + offset])
            (let: (carry,v) := splitmsb (adcB false v1 v2) in
             r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  basicapply (ADD_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))). 
elim: (splitmsb _) => [carry v].
sbazooka.
Qed.   


Lemma XOR_RR_rule (r1 r2:Reg) v1 (v2:DWORD):
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP_Any) (XOR r1, r2)
            (r1~=xorB v1 v2 ** r2~=v2 ** OSZCP false (msb (xorB v1 v2))
                            (xorB v1 v2 == #0) false (lsb (xorB v1 v2))).  
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. 
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP/evalLogicalOp.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma SUB_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (SUB r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalReg_rule. 
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_letGetDWORDSep. rewrite E.
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed.

Lemma ADC_RI_rule (r1:Reg) v1 (v2:DWORD) carry v o s z c p:
  splitmsb (adcB c v1 v2) = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP o s z c p) (ADC r1, v2)
            (r1~=v ** OSZCP (computeOverflow v1 v2 v) (msb v)
                            (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.
  triple_apply evalReg_rule. 
  rewrite /OSZCP.
  triple_apply triple_letGetFlag.
  - by ssimpl.
  rewrite E.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 

Corollary ADD_RM_ruleNoFlags (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (ADD r1, [r2 + offset]) (r1~=addB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any).
Proof.
autorewrite with push_at.
  basicapply (ADD_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))). 
rewrite /OSZCP/OSZCP_Any/stateIsAny/addB/dropmsb/snd.
elim: (splitmsb _) => [carry v].
sbazooka.
Qed.   

Corollary SUB_RM_ruleNoFlags (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (SUB r1, [r2 + offset]) (r1~=subB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any).
Proof.
autorewrite with push_at. rewrite /subB. 
elim E: (sbbB _ _ _) => [carry v].
basicapply (SUB_RM_rule (pd:=pd) (r1:=r1) (r2:=r2) (v1:=v1) (v2:=v2) (offset:=offset)). 
rewrite /OSZCP/OSZCP_Any/stateIsAny/snd. sbazooka. by rewrite E /snd. 
Qed.   


(*---------------------------------------------------------------------------
    AND instruction
  ---------------------------------------------------------------------------*)
(* Generic AND *)
Lemma AND_rule (ds:DstSrc true) (v1: DWORD) :
   |-- specAtDstSrc ds (fun D v2 =>
       basic (D v1 ** OSZCP_Any)
             (BOP true OP_AND ds)
             (let v:= andB v1 v2 in
              D v ** OSZCP false (msb v) (v == #0) false (lsb v))).
Proof.  
  rewrite /specAtDstSrc/DWORDorBYTEregIs. 
  destruct ds. 
  (* RR *)
  specintros => v2. autorewrite with push_at. apply TRIPLE_basic => R.
  repeat (autounfold with eval). 
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
  (* RM *)
  rewrite /specAtMemSpec. 
  elim:src => [optSIB offset].
  elim: optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + specintros => v2 pbase ixval. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    triple_apply evalReg_rule. 
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 
(* Non-indexed *)
  + specintros => v2 pbase. 
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    rewrite /evalDstSrc/evalDstR. 
    triple_apply evalReg_rule.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 
(* Offset only *)
  + specintros => v2.
    autorewrite with push_at. apply TRIPLE_basic => R.
    repeat (autounfold with eval). 
    rewrite /evalDstSrc/evalDstR. 
    triple_apply evalReg_rule. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    rewrite /evalMemSpec.
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setRegSep. 
  (* MR *)
  specintros => v2. rewrite /specAtMemSpecDst. 
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |]. 
  case: ixopt => [[ixr sc] |]. 
(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule.
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpecNone_rule.
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec.
    triple_apply triple_letGetDWORDSep. 
    triple_apply evalReg_rule. 
    triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
  (* RI *)
  apply TRIPLE_basic => R.
  repeat (autounfold with eval).  rewrite /evalDstSrc/evalDstR. 
  triple_apply evalReg_rule. 
  triple_apply triple_pre_introFlags => o sf zf cf pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep.  

  (* MI *)
  rewrite /specAtMemSpecDst. 
  elim:dst => [optSIB offset].
  elim:optSIB => [[base ixopt] |].
  case: ixopt => [[ixr sc] |]. 

(* Indexed *)
  + specintros => pbase ixval. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM.
    triple_apply evalMemSpec_rule. 
    triple_apply triple_letGetDWORDSep.    
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Non-indexed *)
  + specintros => pbase. autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM. 
    triple_apply evalMemSpecNone_rule. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
(* Offset only *)
  + autorewrite with push_at. apply TRIPLE_basic => R. 
    repeat (autounfold with eval). rewrite /evalDstSrc/evalDstM/evalMemSpec. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_pre_introFlags => o s z cf pf. rewrite /OSZCP.
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doSetFlagSep. 
    triple_apply triple_doUpdateZPS. 
    triple_apply triple_setDWORDSep. 
Qed.   

(* AND r1, r2 *)
Corollary AND_RR_rule (r1 r2:Reg) v1 (v2:DWORD) :
  |-- basic (r1~=v1 ** r2 ~= v2 ** OSZCP_Any)
            (AND r1, r2)
            (let v := andB v1 v2 in r1~=v ** r2 ~= v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRR true r1 r2)). Qed.  

(* AND r1, [r2 + offset] *)
Corollary AND_RM_rule (pbase:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) :
  |-- basic (r1~=v1 ** OSZCP_Any)
            (AND r1, [r2 + offset])
            (let v:= andB v1 v2 in r1~=v ** OSZCP false (msb v) (v == #0) false (lsb v)) 
      @ (r2 ~= pbase ** pbase +# offset :-> v2).
Proof. 
  autorewrite with push_at. 
  basicapply (AND_rule (DstSrcRM true r1 (mkMemSpec (Some(r2, None)) #offset))).
Qed. 

Corollary AND_RM_ruleNoFlags (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (AND r1, [r2 + offset]) (r1~=andB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any).
Proof.
autorewrite with push_at. 
basicapply (AND_RM_rule (pbase:=pd) (r1:=r1) (r2:=r2) (v1:=v1) (v2:=v2) (offset:=offset)). 
rewrite /OSZCP/OSZCP_Any/stateIsAny/snd. sbazooka. 
Qed.   


(* AND r, v *)
Lemma AND_RI_rule (r:Reg) v1 (v2:DWORD) :
  |-- basic (r~=v1 ** OSZCP_Any)
            (AND r, v2)
            (let v:= andB v1 v2 in r~=v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof. basicapply (AND_rule (DstSrcRI true r v2)). Qed. 

 
Lemma OR_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  orB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (OR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. rewrite E.
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma XOR_RM_rule (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat) v :
  xorB v1 v2 = v ->
  |-- basic (r1~=v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (XOR r1, [r2 + offset])
            (r1~=v ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  (* Copy-paste of OR_RM_rule proof *)
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. rewrite E.
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 

Corollary OR_RM_ruleNoFlags (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (OR r1, [r2 + offset]) (r1~=orB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any).
Proof.
autorewrite with push_at. 
basicapply (@OR_RM_rule pd r1 r2 v1 v2 offset (orB v1 v2) (refl_equal _)).  
rewrite /OSZCP/OSZCP_Any/stateIsAny/snd. sbazooka. 
Qed.   

Corollary XOR_RM_ruleNoFlags (pd:BITS 32) (r1 r2:Reg) v1 (v2:DWORD) (offset:nat):
  |-- basic (r1~=v1) (XOR r1, [r2 + offset]) (r1~=xorB v1 v2)
             @ (r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any).
Proof.
autorewrite with push_at. 
basicapply (@XOR_RM_rule pd r1 r2 v1 v2 offset (xorB v1 v2) (refl_equal _)).  
rewrite /OSZCP/OSZCP_Any/stateIsAny/snd. sbazooka. 
Qed.   


Lemma SUB_RR_rule (r1 r2:Reg) v1 (v2:DWORD) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** r2~=v2 ** OSZCP_Any) (SUB r1, r2)
            (r1~=v  ** r2~=v2 **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 

Lemma SUB_RI_rule (r1:Reg) v1 (v2:DWORD) carry v:
  sbbB false v1 v2 = (carry,v) ->
  |-- basic (r1~=v1 ** OSZCP_Any) (SUB r1, v2)
            (r1~=v **
             OSZCP (computeOverflow v1 v2 v) (msb v) (v == #0) carry (lsb v)).
Proof.
  (* Copy-paste of ADD_RI_rule proof *)
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  rewrite E. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_setRegSep. 
Qed. 


Lemma CMP_RI_rule (r1:Reg) v1 (v2:DWORD) carry res:
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** OSZCP_Any) (CMP r1, v2)
            (r1 ~= v1 ** OSZCP (computeOverflow v1 v2 res) (msb res)
                         (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  rewrite E.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. 
Qed. 

Lemma CMP_RbI_rule (r1:BYTEReg) (v1 v2:BYTE) carry res:
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (BYTEregIs r1 v1 ** OSZCP_Any) (BOP false OP_CMP (DstSrcRI false r1 v2))
            (BYTEregIs r1 v1 ** OSZCP (computeOverflow v1 v2 res) (msb res) (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR.
  triple_apply evalBYTEReg_rule.
  rewrite E.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. 
Qed. 

Lemma CMP_RI_eq_rule (r1:Reg) v1 (v2:DWORD):
  |-- basic (r1 ~= v1 ** OSZCP_Any) (CMP r1, v2)
            (r1 ~= v1 ** OF? ** SF? ** CF? ** PF? ** 
                         ZF ~= (v1==v2)).
Proof.
case E: (sbbB false v1 v2) => [carry res]. 
eapply basic_basic.
apply (CMP_RI_rule E).
by ssimpl.  
rewrite /OSZCP/stateIsAny. sbazooka. 
have: res = subB v1 v2. 
rewrite /subB. by rewrite E.  
move ->.
by rewrite subB_eq0. 
Qed. 

Lemma CMP_MbR_eq_rule (r1:Reg) (r2: BYTEReg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OSZCP_Any) (CMP [r1], r2)
            (r1 ~= p ** BYTEregIs r2 v2 ** p :-> v1 ** OF? ** SF? ** CF? ** PF? ** 
                         ZF ~= (v1==v2)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR/evalDstM.
  triple_apply evalMemSpecNone_rule.
  rewrite addB0/scaleBy.
  triple_apply triple_letGetBYTESep. 
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply evalBYTEReg_rule. 
case E: (sbbB false v1 v2) => [carry res].   
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. rewrite /stateIsAny.
  sbazooka. 
  have H:= (subB_eq0 v1 v2). rewrite /subB in H.
  rewrite E in H. by rewrite H. 
Qed. 

Lemma CMP_MbI_eq_rule (r1:Reg) (p:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** p :-> v1 ** OSZCP_Any) (CMP BYTE [r1], v2)
            (r1 ~= p ** p :-> v1 ** OF? ** SF? ** CF? ** PF? ** 
                         ZF ~= (v1==v2)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR/evalDstM.
  triple_apply evalMemSpecNone_rule.
  rewrite addB0/scaleBy.
  triple_apply triple_letGetBYTESep. 
case E: (sbbB false v1 v2) => [carry res].   
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. rewrite /stateIsAny.
  sbazooka. 
  have H:= (subB_eq0 v1 v2). rewrite /subB in H.
  rewrite E in H. by rewrite H.
Qed. 


Lemma CMP_MbxI_eq_rule (r1:Reg) (r2:NonSPReg) (p ix:DWORD) (v1 v2:BYTE):
  |-- basic (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OSZCP_Any) (CMP BYTE [r1 + r2 + 0], v2)
            (r1 ~= p ** r2 ~= ix ** addB p ix :-> v1 ** OF? ** SF? ** CF? ** PF? ** 
                         ZF ~= (v1==v2)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR/evalDstM.
  triple_apply evalMemSpec_rule.
  rewrite addB0/scaleBy.
  triple_apply triple_letGetBYTESep. 
case E: (sbbB false v1 v2) => [carry res].   
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip.
  rewrite /stateIsAny.  sbazooka. 
  have H:= (subB_eq0 v1 v2). rewrite /subB in H.
  rewrite E in H. by rewrite H. 
Qed. 


Lemma CMP_RbI_eq_rule (r1:BYTEReg) (v1 v2:BYTE):
  |-- basic (BYTEregIs r1 v1 ** OSZCP_Any) (BOP false OP_CMP (DstSrcRI false r1 v2))
            (BYTEregIs r1 v1 ** OF? ** SF? ** CF? ** PF? ** 
                         ZF ~= (v1==v2)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval.  
  rewrite /evalDstSrc/evalDstR/evalDstM.
  triple_apply evalBYTEReg_rule.
case E: (sbbB false v1 v2) => [carry res].   
  triple_apply triple_pre_introFlags => o s z c pf. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip.
  rewrite /stateIsAny. sbazooka. 
  have H:= (subB_eq0 v1 v2). rewrite /subB in H. rewrite E in H. 
  by rewrite H. 
Qed. 


Lemma CMP_RM_rule (pd:BITS 32) (r1 r2:Reg) offset (v1 v2:DWORD) carry res :
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (CMP r1, [r2+offset])
            (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v1 v2 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  autounfold with eval. rewrite  /evalDstSrc/evalDstR.
  triple_apply evalReg_rule.
  rewrite /evalMemSpec.
  triple_apply evalReg_rule. 
  triple_apply triple_letGetDWORDSep. rewrite E. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. 
Qed. 


Lemma CMP_MR_rule (pd:BITS 32) (r1 r2:Reg) offset (v1 v2:DWORD) carry res:
  sbbB false v2 v1 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 ** OSZCP_Any)
            (CMP [r2+offset], r1)
            (r1 ~= v1 ** r2 ~= pd ** pd +# offset :-> v2 **
             OSZCP (computeOverflow v2 v1 res) (msb res)
                   (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  autounfold with eval. rewrite /evalDstSrc.
  triple_apply evalMemSpecNone_rule. 
  triple_apply triple_letGetDWORDSep. 
  triple_apply evalReg_rule. rewrite E. 
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip. 
Qed. 

Lemma CMP_RR_rule (r1 r2:Reg) v1 (v2:DWORD) carry res:
  sbbB false v1 v2 = (carry, res) ->
  |-- basic (r1 ~= v1 ** r2 ~= v2 ** OSZCP_Any) (CMP r1, r2)
            (r1 ~= v1 ** r2 ~= v2 **
              OSZCP (computeOverflow v1 v2 res) (msb res)
                    (res == #0) carry (lsb res)).
Proof.
  move => E. apply TRIPLE_basic => R.
  autounfold with eval. 
  rewrite /evalDstSrc/evalDstR.
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule.
  rewrite E.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS. 
  triple_apply triple_skip. 
Qed.

Lemma TEST_self_rule (r:Reg) (v:DWORD) :
  |-- basic (r ~= v ** OSZCP_Any) (TEST r, r)
            (r ~= v ** OSZCP false (msb v) (v == #0) false (lsb v)).
Proof.
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR/evalRegImm.
  triple_apply evalReg_rule. 
  triple_apply evalReg_rule. rewrite andBB.
  triple_apply triple_pre_introFlags => o s z c p. rewrite /OSZCP.
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doSetFlagSep. 
  triple_apply triple_doUpdateZPS.
  triple_apply triple_skip. 
Qed. 


(* Lazy man's proof *)
Lemma SmallCount : forall count, count < 32 -> toNat (n:=8) (andB #x"1f" (fromNat count)) = count. 
Proof. do 32 case => //. 
Qed. 

Lemma SHL_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 -> 
  |-- basic (r~=v ** OSZCP_Any) (SHL r, count)
            (r~=iter count shlB v ** OSZCP_Any).
Proof.
  move => BOUND. 
  apply TRIPLE_basic => R.
  repeat autounfold with eval. rewrite /evalDst/evalDstR.
  triple_apply evalReg_rule. 
  rewrite /evalShiftCount/evalShiftOp. rewrite id_l.
  rewrite (SmallCount BOUND). 
  case E: count => [| count'].   
  + replace (iter _ _ v) with v by done. 
    triple_apply triple_setRegSep. 

  + 
  triple_apply triple_pre_introFlags => o s z c p. 
  rewrite /OSZCP_Any/OSZCP/stateIsAny. 
  triple_apply triple_doSetFlagSep. 
  case E': count' => [| count''].     
  + triple_apply triple_doSetFlagSep. 
    triple_apply triple_setRegSep. rewrite dropmsb_iter_shlB.
    sbazooka.  
  + triple_apply triple_doForgetFlagSep. 
    triple_apply triple_setRegSep.
    rewrite dropmsb_iter_shlB.     
    rewrite /stateIsAny. sbazooka. 
Qed. 

Lemma SHR_RI_rule (r:Reg) (v:DWORD) (count:nat):
  count < 32 -> 
  |-- basic (r~=v ** OSZCP_Any) (SHR r, count)
            (r~=iter count shrB v ** OSZCP_Any).
Proof.
  move => BOUND. 
  apply TRIPLE_basic => R.
  rewrite /evalInstr/evalDst/evalDstR.
  triple_apply evalReg_rule. 
  rewrite /evalShiftCount/evalShiftOp id_l.
  rewrite (SmallCount BOUND). 
  case E: count => [| count'].   
  + replace (iter _ _ v) with v by done. 
    triple_apply triple_setRegSep. 

  + 
  triple_apply triple_pre_introFlags => o s z c p. 
  rewrite /OSZCP_Any/OSZCP/stateIsAny.
  triple_apply triple_doSetFlagSep. 
  case E': count' => [| count''].     
  + triple_apply triple_doSetFlagSep. 
    triple_apply triple_setRegSep. rewrite droplsb_iter_shrB.
    sbazooka.  
  + triple_apply triple_doForgetFlagSep. 
    triple_apply triple_setRegSep.
    rewrite droplsb_iter_shrB.     
    rewrite /stateIsAny. sbazooka. 
Qed. 

(*---------------------------------------------------------------------------
    Now, rules that involve control-flow.
  ---------------------------------------------------------------------------*)

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

Lemma triple_letGetCondition cc (v:bool) (P Q: SPred) c: 
  TRIPLE (ConditionIs cc v ** P) (c v) Q -> 
  TRIPLE (ConditionIs cc v ** P) (bind (evalCondition cc) c) Q.
Proof. 
  rewrite /evalCondition /ConditionIs => H. destruct cc.
  - (* CC_O *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_C *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_Z *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_BE *)
    apply triple_pre_existsSep => fc. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. 
    subst v. 
    triple_apply H; sbazooka. 
  - (* CC_S *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_P *)
    triple_apply triple_letGetFlag; by [ssimpl|].
  - (* CC_L *)
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.   
    triple_apply H; sbazooka. 
  - (* CC_LE *)
    apply triple_pre_existsSep => fs. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fo. triple_apply triple_letGetFlag.
    - by sbazooka.
    apply triple_pre_existsSep => fz. triple_apply triple_letGetFlag.
    - by sbazooka.
    rewrite /lpropand. apply triple_pre_existsSep => Hv. inversion Hv. subst v.
    triple_apply H; sbazooka. 
Qed. 

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD) :
  |-- interpJmpTgt tgt q (fun P addr =>
     (|> safe @ (EIP ~= addr ** P) -->> safe @ (EIP ~= p ** P)) <@ (p -- q :-> JMPrel tgt)).
Proof.
  rewrite /interpJmpTgt. destruct tgt.  
  (* JmpTgtI *)
  destruct t. apply TRIPLE_safe => R.
  rewrite /evalInstr/evalSrc/evalJmpTgt. 
  triple_apply triple_letGetRegSep.
  triple_apply triple_setRegSep. 

  (* JmpTgtM *)
  destruct m. 
  case: sib => [[base indexAndScale] |].
  - destruct indexAndScale.
    destruct p0 as [rix sc]. 
    rewrite /interpMemSpecSrc. 
    specintros => pase ixval addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg. 
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetRegSep. 
    triple_apply triple_letGetDWORDSep. 
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc. 
    specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg. 
    triple_apply triple_letGetRegSep.
    triple_apply triple_letGetDWORDSep. 
    by triple_apply triple_setRegSep.
    rewrite /interpMemSpecSrc. 
    specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr/evalJmpTgt/evalMemSpec/evalRegMem /evalReg. 
    triple_apply triple_letGetDWORDSep. 
    by triple_apply triple_setRegSep.

  (* JmpTgtR *)
  specintros => addr. 
  apply TRIPLE_safe => R.
  rewrite /evalInstr/evalJmpTgt /evalRegMem /evalReg /evalPush.  
  triple_apply triple_letGetRegSep. 
  by triple_apply triple_setRegSep.
Qed. 


(* For convenience, the ~~b branch is not under a |> operator since q will
   never be equal to p, and thus there is no risk of recursion. *)
Lemma JCCrel_rule rel cc cv (b:bool) (p q: DWORD) :
  |-- (
      |> safe @ (b == cv /\\ EIP ~= (addB q rel) ** ConditionIs cc b) //\\
         safe @ (b == (~~cv) /\\ EIP ~= q ** ConditionIs cc b) -->>
      safe @ (EIP ~= p ** ConditionIs cc b)
    ) <@ (p -- q :-> JCCrel cc cv (mkTgt rel)).
Proof.
  Import Setoid.
  rewrite ->(spec_later_weaken (safe @ (b == (~~ cv) /\\ EIP~=q ** ConditionIs cc b))).
  rewrite <-spec_later_and. rewrite ->spec_at_and_or; last apply _.
  apply TRIPLE_safe => R. rewrite /evalInstr.
  triple_apply triple_letGetCondition.
  replace (b == (~~cv)) with (~~(b == cv)); last first.
  - case: b; case: cv; reflexivity.
  case: (b == cv).
  - triple_apply triple_letGetRegSep. 
    triple_apply triple_setRegSep.
    apply: lorR1. ssplit => //. 
  - triple_apply triple_skip. 
    apply: lorR2. by sbazooka.
Qed.

Lemma RET_rule p' (sp:BITS 32) (offset:WORD) (p q: DWORD) :
  let sp':BITS 32 := addB (sp+#4) (zeroExtend 16 offset) in
  |-- (
      |> safe @ (EIP ~= p' ** ESP ~= sp' ** sp :-> p') -->>
         safe @ (EIP ~= p  ** ESP ~= sp  ** sp :-> p')
    ) <@ (p -- q :-> RETOP offset).
Proof.
  apply TRIPLE_safe => R.
  rewrite /evalInstr.
  triple_apply triple_letGetRegSep.  
  triple_apply triple_letGetDWORDSep. 
  triple_apply triple_doSetRegSep. 
  triple_apply triple_setRegSep. 
Qed.

Lemma CALLrel_rule (p q: DWORD) (tgt: JmpTgt) (w sp:DWORD) :
  |-- interpJmpTgt tgt q (fun P p' =>
      (
      |> safe @ (EIP ~= p' ** P ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** P ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel tgt)).
Proof.
  rewrite /interpJmpTgt.
  destruct tgt.

  (* JmpTgtI *)
  destruct t. 
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg. 
  triple_apply triple_letGetRegSep. 
  rewrite /evalJmpTgt.
  triple_apply triple_letGetRegSep. 
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule. 

  (* JmpTgtM *)
  destruct m. 
  - case: sib => [[base indexAndScale] |]. 
    destruct indexAndScale.
    destruct p0 as [rix sc]. 
    rewrite /interpMemSpecSrc. specintros => pbase indexval addr. 
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg. 
    triple_apply triple_letGetRegSep. 
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep. 
    triple_apply triple_letGetRegSep. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_doSetRegSep.
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => pbase addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg. 
    triple_apply triple_letGetRegSep. 
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetRegSep. 
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_doSetRegSep. 
    by triple_apply evalPush_rule.
    rewrite /interpMemSpecSrc. specintros => addr.
    apply TRIPLE_safe => R.
    rewrite /evalInstr /evalRegMem /evalReg. 
    triple_apply triple_letGetRegSep. 
    rewrite /evalJmpTgt/evalMemSpec.
    triple_apply triple_letGetDWORDSep. 
    triple_apply triple_doSetRegSep. 
    by triple_apply evalPush_rule.

  (* JmpTgtR *)
  specintros => addr. 
  apply TRIPLE_safe => R.
  rewrite /evalInstr /evalRegMem /evalReg. 
  triple_apply triple_letGetRegSep. 
  triple_apply triple_letGetRegSep. 
  triple_apply triple_doSetRegSep.
  by triple_apply evalPush_rule.
Qed. 

Corollary CALLrel_R_rule (r:Reg) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, Forall p', (
      |> safe @ (EIP ~= p' ** r~=p' ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** r~=p' ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel r).
Proof. 
  specintros => w sp p'.
  Hint Unfold interpJmpTgt : specapply. 
  specapply (CALLrel_rule p q (JmpTgtR r)). sbazooka.

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at. 
  cancel1. cancel1. sbazooka.   
Qed. 

Corollary CALLrel_I_rule (rel: DWORD) (p q: DWORD) :
  |-- Forall w: DWORD, Forall sp:DWORD, (
      |> safe @ (EIP ~= addB q rel ** ESP~=sp-#4 ** sp-#4 :-> q) -->>
         safe @ (EIP ~= p  ** ESP~=sp    ** sp-#4 :-> w)
    ) <@ (p -- q :-> CALLrel rel).
Proof. 
  specintros => w sp. 
  specapply (CALLrel_rule p q (JmpTgtI rel)). sbazooka. 

  (* Should be able to automate this! *)
  rewrite <-spec_reads_frame. apply limplValid. autorewrite with push_at. 
  cancel1. cancel1. sbazooka. 
Qed. 


(* unconditional jump *)
Lemma JMPrel_I_rule rel (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addB q rel) -->> safe @ (EIP ~= p)) <@
        (p -- q :-> JMPrel (mkTgt rel)).
Proof.
  specapply (JMPrel_rule (JmpTgtI (mkTgt rel))). by ssimpl.  
  
  autorewrite with push_at. rewrite <-spec_reads_frame. apply limplValid. 
  cancel1. cancel1. sbazooka. 
Qed. 

Lemma JMPrel_R_rule (r:Reg) addr (p q: DWORD) :
  |-- (|> safe @ (EIP ~= addr ** r ~= addr) -->> safe @ (EIP ~= p ** r ~= addr)) <@
        (p -- q :-> JMPrel (JmpTgtR r)).
Proof.
  specapply (JMPrel_rule (JmpTgtR r)). by ssimpl. 

  rewrite <-spec_reads_frame. autorewrite with push_at. rewrite limplValid. 
  cancel1. cancel1. sbazooka. 
Qed. 

End InstrRules.