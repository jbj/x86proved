(*===========================================================================
    Instruction evaluator
  ===========================================================================*)
Require Import ssreflect ssrnat ssrbool eqtype tuple.
Require Import bitsops instr monad reader procstate procstatemonad exn.
Require Import common_definitions.

Definition updateZPS {n} (result: BITS n) :=
  do! updateFlagInProcState ZF (result == #0);
  do! updateFlagInProcState PF (lsb result);
  updateFlagInProcState SF (msb result).


Definition evalArithOp {n}
  (f : bool -> BITS n -> BITS n -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let! c = getFlagFromProcState CF;
  let (c, result) := eta_expand (f c arg1 arg2) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithOpNoCarry {n}
  (f : bool -> BITS n -> BITS n -> bool * BITS n) (arg1 arg2: BITS n)  :=
  let (c,result) := eta_expand (f false arg1 arg2) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (computeOverflow arg1 arg2 result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOp {n} (f : BITS n -> bool*BITS n) arg  :=
  let (c,result) := eta_expand (f arg) in
  do! updateFlagInProcState CF c;
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalArithUnaryOpNoCarry {n} (f : BITS n -> BITS n) arg  :=
  let result := f arg in
  do! updateFlagInProcState OF (msb arg != msb result);
  do! updateZPS result;
  retn result.

Definition evalLogicalOp {n} (f : BITS n -> BITS n -> BITS n) arg1 arg2 :=
  let result := f arg1 arg2 in
  do! updateFlagInProcState CF false;
  do! updateFlagInProcState OF false;
  do! updateZPS result;
  retn result.

Definition evalBinOp {n} op : BITS n -> BITS n -> ST (BITS n) :=
  match op with
  | OP_ADC => evalArithOp adcB
  | OP_ADD => evalArithOpNoCarry adcB
  | OP_AND => evalLogicalOp andB
  | OP_OR  => evalLogicalOp orB
  | OP_SBB => evalArithOp sbbB
  | OP_SUB => evalArithOpNoCarry sbbB
  | OP_CMP => evalArithOpNoCarry sbbB
  | OP_XOR => evalLogicalOp xorB
  end.

Definition evalShiftOp {n} (op: ShiftOp)(arg: BITS n.+1) (count:BYTE) : ST (BITS n.+1) :=
  let count := toNat (andB #x"1f" count) in
  (* If the count is zero then no flags are changed, argument is left alone *)
  if count is 0 then retn arg
  else

  (* Otherwise we mess with the carry flag *)
  let! (o, c, res) =
    match op with
    | OP_ROL => let res:= iter count rolB arg
                in retn (xorb (lsb res) (msb res), lsb res, res)

    | OP_ROR => let res:= iter count rorB arg
                in retn (xorb (msb res) (msb (dropmsb res)), msb res, res)

    | OP_RCL => let! carry = getFlagFromProcState CF;
                let res:= iter count rolB (joinmsb(carry, arg))
                in retn (xorb (lsb res) (msb res), msb res, dropmsb res)

    | OP_RCR => let! carry = getFlagFromProcState CF;
                let res := iter count rorB (joinlsb(arg, carry))
                in retn (xorb (msb res) (msb (dropmsb res)), lsb res, droplsb res)

    | OP_SHL | OP_SAL => let res:= iter count shlB (joinmsb(false,arg))
                in retn (xorb (msb arg) (msb (dropmsb arg)), msb res, dropmsb res)

    | OP_SHR => let res := iter count shrB (joinlsb(arg,false))
                in retn (msb arg, lsb res, droplsb res)

    | OP_SAR => let res := iter count sarB (joinlsb(arg,false))
                in retn (false, lsb res, droplsb res)
    end;
  do! updateFlagInProcState CF c;
  do! (if count is 1 then updateFlagInProcState CF o else forgetFlagInProcState OF);
  retn res.

Definition evalUnaryOp {n} op : BITS n -> ST (BITS n) :=
  match op with
  | OP_INC => evalArithUnaryOpNoCarry incB
  | OP_DEC => evalArithUnaryOpNoCarry decB
  | OP_NOT => fun arg => retn (invB arg)
  | OP_NEG => evalArithUnaryOp (fun arg => (arg != #0, negB arg))
  end.

Definition evalCondition cc : ST bool :=
  match cc with
  | CC_O => getFlagFromProcState OF
  | CC_B => getFlagFromProcState CF
  | CC_Z => getFlagFromProcState ZF
  | CC_BE => let! cf = getFlagFromProcState CF; let! zf = getFlagFromProcState ZF; retn (cf || zf)
  | CC_S => getFlagFromProcState SF
  | CC_P => getFlagFromProcState PF
  | CC_L => let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; retn (xorb sf f)
  | CC_LE =>
    let! sf = getFlagFromProcState SF; let! f = getFlagFromProcState OF; let! zf = getFlagFromProcState ZF;
    retn ((xorb sf f) || zf)
  end.


Definition scaleBy s (d: DWORD) :=
  match s with
  | S1 => d
  | S2 => shlB d
  | S4 => shlB (shlB d)
  | S8 => shlB (shlB (shlB d))
  end.

(* Evaluation functions for various syntactic entities *)
Definition evalReg (r: Reg) := getRegFromProcState r.
Definition evalBYTEReg (r: BYTEReg) :=
  match r with
  | AL => let! d = getRegFromProcState EAX; retn (low 8 d)
  | BL => let! d = getRegFromProcState EBX; retn (low 8 d)
  | CL => let! d = getRegFromProcState ECX; retn (low 8 d)
  | DL => let! d = getRegFromProcState EDX; retn (low 8 d)
  | AH => let! d = getRegFromProcState EAX; retn (low 8 (@high 24 8 d))
  | BH => let! d = getRegFromProcState EBX; retn (low 8 (@high 24 8 d))
  | CH => let! d = getRegFromProcState ECX; retn (low 8 (@high 24 8 d))
  | DH => let! d = getRegFromProcState EDX; retn (low 8 (@high 24 8 d))
  end.

Definition evalDWORDorBYTEReg (dword:bool) : DWORDorBYTEReg dword -> ST (DWORDorBYTE dword) :=
  if dword as dword return DWORDorBYTEReg dword -> ST (DWORDorBYTE dword)
  then evalReg else evalBYTEReg.

Definition evalMemSpec m :=
  match m with
    mkMemSpec optSIB offset =>
    if optSIB is Some(base,ixopt)
    then
      let! baseval = getRegFromProcState base;
      let p := addB baseval offset in
      if ixopt is Some(index,sc)
      then
        let! indexval = getRegFromProcState index;
        retn (addB p (scaleBy sc indexval))
      else retn p
    else retn offset
  end.

Definition evalSrc src :=
  match src with
  | SrcI c => retn c
  | SrcR r => evalReg r
  | SrcM m =>
    let! p = evalMemSpec m;
    getDWORDFromProcState p
  end.

Definition evalJmpTgt tgt :=
  match tgt with
  | JmpTgtI (mkTgt r) =>
    let! nextIP = getRegFromProcState EIP;
    retn (addB nextIP r)
  | JmpTgtR r => evalReg r
  | JmpTgtM m =>
    let! p = evalMemSpec m;
    getDWORDFromProcState p
  end.

Definition setBYTERegInProcState (r: BYTEReg) (b: BYTE) :=
  match r with
  | AL =>
    let! r = getRegFromProcState EAX;
    setRegInProcState EAX (@high 24 8 r ## b)

  | BL =>
    let! r = getRegFromProcState EBX;
    setRegInProcState EBX (@high 24 8 r ## b)

  | CL =>
    let! r = getRegFromProcState ECX;
    setRegInProcState ECX (@high 24 8 r ## b)

  | DL =>
    let! r = getRegFromProcState EDX;
    setRegInProcState EDX (@high 24 8 r ## b)

  | AH =>
    let! r = getRegFromProcState EAX;
    setRegInProcState EAX (@high 16 16 r ## b ## low 8 r)

  | BH =>
    let! r = getRegFromProcState EBX;
    setRegInProcState EBX (@high 16 16 r ## b ## low 8 r)

  | CH =>
    let! r = getRegFromProcState ECX;
    setRegInProcState ECX(@high 16 16 r ## b ## low 8 r)

  | DH =>
    let! r = getRegFromProcState EDX;
    setRegInProcState EDX (@high 16 16 r ## b ## low 8 r)
  end.

Definition setDWORDorBYTERegInProcState (dword:bool) :
  DWORDorBYTEReg dword -> DWORDorBYTE dword -> _ :=
  if dword as dword return DWORDorBYTEReg dword -> DWORDorBYTE dword -> _
  then setRegInProcState else setBYTERegInProcState.

Definition evalDstR (dword:bool) (drop: bool) (r:DWORDorBYTEReg dword) :=
    fun (op : DWORDorBYTE dword -> ST (DWORDorBYTE dword)) =>
    let! rval = evalDWORDorBYTEReg dword r;
    let! result = op rval;
    if drop then retn tt else setDWORDorBYTERegInProcState dword r result.

Definition evalDstM (dword:bool) (drop: bool) m
  (op: DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
    let! a = evalMemSpec m;
    let! v = getDWORDorBYTEFromProcState dword a;
    let! result = op v;
    if drop then retn tt
    else setDWORDorBYTEInProcState (dword:=dword) a result.

Definition evalDst dword drop (dst: RegMem dword)
  (op: DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
  match dst with
  | RegMemR r => evalDstR dword drop r op
  | RegMemM m => evalDstM dword drop m op
  end.

Definition evalRegMem dword (rm: RegMem dword) :=
  match rm with
  | RegMemR r => evalDWORDorBYTEReg dword r
  | RegMemM m => let! a = evalMemSpec m; getDWORDorBYTEFromProcState dword a
  end.

Definition evalRegMemBYTE (rm: RegMem false) :=
  match rm with
  | RegMemR r => evalBYTEReg r
  | RegMemM m => let! a = evalMemSpec m; getBYTEFromProcState a
  end.

Definition evalRegMemWORD (rm: RegMem true) :=
  match rm with
  | RegMemR r => let! d = evalReg r; retn (low 16 d)
  | RegMemM m => let! a = evalMemSpec m; getWORDFromProcState a
  end.


Definition evalRegImm {dword} (ri: RegImm dword)  :=
  match ri with
  | RegImmR r => evalDWORDorBYTEReg dword r
  | RegImmI c => retn c
  end.

Definition evalShiftCount (c: ShiftCount) :=
  match c with
  | ShiftCountCL => evalBYTEReg CL
  | ShiftCountI c => retn c
  end.

Definition evalDstSrc {dword} (drop: bool) (ds: DstSrc dword)
  (op: DWORDorBYTE dword -> DWORDorBYTE dword -> ST (DWORDorBYTE dword)) :=
  match ds with
  | DstSrcRR dst src =>
    evalDstR dword drop dst (fun a => let! rval = evalDWORDorBYTEReg dword src; op a rval)

  | DstSrcRM dst src =>
    evalDstR dword drop dst (fun v1 => let! a = evalMemSpec src;
                                       let! v2 = getDWORDorBYTEFromProcState _ a; op v1 v2)

  | DstSrcMR dst src =>
    evalDstM _ drop dst (fun a => let! rval = evalDWORDorBYTEReg dword src; op a rval)

  | DstSrcRI dst c   =>
    evalDstR dword drop dst (fun a => op a c)

  | DstSrcMI dst c   =>
    evalDstM _ drop dst (fun a => op a c)
  end.


Definition evalMOV {dword} (ds: DstSrc dword) :=
  match ds with
  | DstSrcRR dst src =>
    let! v = evalDWORDorBYTEReg dword src;
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcRM dst src =>
    let! a = evalMemSpec src;
    let! v = getDWORDorBYTEFromProcState _ a;
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcMR dst src =>
    let! v = evalDWORDorBYTEReg dword src;
    let! a = evalMemSpec dst;
    setDWORDorBYTEInProcState a v

  | DstSrcRI dst v   =>
    setDWORDorBYTERegInProcState dword dst v

  | DstSrcMI dst v   =>
    let! a = evalMemSpec dst;
    setDWORDorBYTEInProcState a v
  end.


Definition evalPush (v: DWORD) : ST unit :=
  let! oldSP = getRegFromProcState ESP;
  do! setRegInProcState ESP (oldSP-#4);
  setDWORDInProcState (oldSP-#4) v.

Definition evalInstr instr : ST unit :=
  match instr with
  | POP dst =>
    let! oldSP = getRegFromProcState ESP;
    do! evalDst true false dst (fun d => getDWORDFromProcState oldSP);
    setRegInProcState ESP (oldSP+#4)

  | UOP dword op dst =>
    evalDst dword false dst (evalUnaryOp op)

  | MOVOP dword ds =>
    evalMOV ds

  | MOVX signextend false dst src =>
    let! v = evalRegMemBYTE src;
    setRegInProcState dst (if signextend then signExtend n24 v else zeroExtend n24 v)

  | MOVX signextend true dst src =>
    let! v = evalRegMemWORD src;
    setRegInProcState dst (if signextend then signExtend n16 v else zeroExtend n16 v)

    (* @todo akenn: implement bit operations *)
  | BITOP op dst b =>
    raiseExn ExnUD

  | BOP dword op ds =>
    evalDstSrc (match op with OP_CMP => true | _ => false end) ds
    (fun d s => evalBinOp op d s)

  | TESTOP dword dst src =>
    evalDst dword true dst
    (fun d => let! s = evalRegImm src; evalBinOp OP_AND d s)

  | SHIFTOP true op dst count =>
    evalDst true false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n31) op d c)

  | SHIFTOP false op dst count =>
    evalDst false false dst
    (fun d => let! c = evalShiftCount count; evalShiftOp (n:=n7) op d c)

  | IMUL dst src =>
    raiseExn ExnUD

  | MUL true src =>
    let! v1 = getRegFromProcState EAX;
    let! v2 = evalRegMem true src;
    let res := fullmulB v1 v2 in
    let cfof := high n32 res == #0 in
    do! setRegInProcState EAX (low n32 res);
    do! setRegInProcState EDX (high n32 res);
    do! updateFlagInProcState CF cfof;
    do! updateFlagInProcState OF cfof;
    do! forgetFlagInProcState SF;
    do! forgetFlagInProcState PF;
    forgetFlagInProcState ZF

  | LEA r (RegMemM m) =>
    let! a = evalMemSpec m;
    setRegInProcState r a

  | LEA r (RegMemR _) =>
    raiseExn ExnUD

  | XCHG d r1 (RegMemR r2) =>
    let! v1 = evalDWORDorBYTEReg _ r1;
    let! v2 = evalDWORDorBYTEReg _ r2;
    do! setDWORDorBYTERegInProcState _ r1 v2;
    setDWORDorBYTERegInProcState _ r2 v1

  | XCHG d r (RegMemM ms) =>
    let! v1 = evalDWORDorBYTEReg _ r;
    let! addr = evalMemSpec ms;
    let! v2 = getDWORDorBYTEFromProcState _ addr;
    do! setDWORDorBYTERegInProcState _ r v2;
    setDWORDorBYTEInProcState addr v1

  | JMPrel src =>
    let! newIP = evalJmpTgt src;
    setRegInProcState EIP newIP

  | JCCrel cc cv (mkTgt tgt) =>
    let! b = evalCondition cc;
    if b == cv then
      let! oldIP = getRegFromProcState EIP;
      setRegInProcState EIP (addB oldIP tgt)
    else
      retn tt

  | CLC =>
    updateFlagInProcState CF false


  | STC =>
    updateFlagInProcState CF true

  | CMC =>
    let! c = getFlagFromProcState CF;
    updateFlagInProcState CF (negb c)

    (* Actually, this should loop *)
  | HLT =>
    retn tt

  | BADINSTR =>
    raiseExn ExnUD

  | PUSH src =>
    let! v = evalSrc src;
    evalPush v

  | CALLrel src =>
    let! oldIP = getRegFromProcState EIP;
    let! newIP = evalJmpTgt src;
    do! setRegInProcState EIP newIP;
    evalPush oldIP
(*=evalRET *)
  | RETOP offset =>
    let! oldSP = getRegFromProcState ESP;
    let! IP' = getDWORDFromProcState oldSP;
    do! setRegInProcState ESP
      (addB (oldSP+#n4) (zeroExtend n16 offset));
    setRegInProcState EIP IP'
(*=End *)

(*
  | IN dword port =>
    let! d = inputST port;
    setRegInProcState EAX (zeroExtend _ d)
*)

  | OUT false port =>
    let! data = evalBYTEReg AL;
    outputOnChannel port data

  | _ =>
    raiseUnspecified

  end.
