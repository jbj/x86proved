(** * JMP (rel) instruction *)
Require Import x86proved.x86.instrrules.core.
Import x86.instrrules.core.instrruleconfig.

Require Import x86proved.spectac (* for [specapply] *).
Require Import x86proved.common_tactics (* for [evar_safe_reflexivity] *).
Require Import x86proved.basicspectac (* for [specapply *] *).
Require Import x86proved.chargetac (* for [finish_logic] *).

Lemma JMPrel_rule (tgt: JmpTgt) (p q: DWORD) 
: |-- interpJmpTgt tgt q (fun P addr =>
                            ((|> safe  @ (EIP ~= addr ** P)
                            -->> safe @ (EIP ~= p ** P)) @ (p -- q :-> JMPrel tgt))).
Proof.
  rewrite /interpJmpTgt/interpMemSpecSrc.
  do_instrrule
    (try specintros => *;
     apply: TRIPLE_safeLater => ?;
     do !instrrule_triple_bazooka_step idtac).
Qed.

(** We make this rule an instance of the typeclass, and leave
    unfolding things like [specAtDstSrc] to the getter tactic
    [get_instrrule_of]. *)
Global Instance: forall (tgt : JmpTgt), instrrule (JMPrel tgt) := @JMPrel_rule.

Section specapply_hint.
Local Hint Unfold interpJmpTgt : specapply.

Lemma JMPrel_I_rule (rel: DWORD) (p q: DWORD):
  |-- ((|> safe @ (EIP ~= addB q rel)
           -->> safe @ (EIP ~= p)) @ (p -- q :-> JMPrel rel)).
Proof. supersafeapply (JMPrel_rule rel). finish_logic. Qed.

Lemma JMPrel_R_rule (r:Reg) (addr: DWORD) (p q: DWORD) :
  |-- ((|> safe @ (EIP ~= addr ** r ~= addr)
           -->> safe @ (EIP ~= p ** r ~= addr)) @ (p -- q :-> JMPrel r)).
Proof. supersafeapply (JMPrel_rule r). finish_logic. Qed.

End specapply_hint.
