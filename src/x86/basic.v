(*===========================================================================
  Definition of Hoare triple for arbitrary code-like data
  For store assertions P and Q and "code" c, we write
     basic P c Q
  to mean
     for any addresses i and j that point to code c,
     if   it's safe to run from EIP=j with assertion Q
     then it's safe to run from EIP=i with assertion P
  ===========================================================================*)
Require Import ssreflect ssrbool ssrnat eqtype seq fintype.
Require Import procstate procstatemonad bitsops bitsprops bitsopsprops.
Require Import SPred septac spec spectac safe pointsto cursor instr reader instrcodec.
Require Import Setoid RelationClasses Morphisms.

Section Basic.
  Context {T} `{MI: MemIs T}.

  (** Basic block of position-independent code *)
  Definition basic P (c:T) Q : spec :=
    Forall i j:DWORD,
    (safe @ (EIP ~= j ** Q) -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> c).
  Global Strategy 10000 [basic].

  (* Experimental: multiple alternative exits *)
  Fixpoint otherExits (Qs: seq (DWORD * SPred)) : spec :=
  if Qs is (i,Q)::Qs'
  then |> safe @ (EIP ~= i ** Q) //\\ otherExits Qs'
  else ltrue.

  Definition multiexit P (c:T) Q Qs : spec :=
    Forall i j:DWORD,
    ((safe @ (EIP ~= j ** Q) //\\ otherExits Qs) -->> safe @ (EIP ~= i ** P)) <@ (i -- j :-> c).

  (* Push spec through basic *)
  Lemma spec_at_basic P c Q R :
    basic P c Q @ R -|- basic (P ** R) c (Q ** R).
  Proof.
    rewrite /basic.
    autorewrite with push_at. cancel1 => i.
    autorewrite with push_at. cancel1 => j.
    autorewrite with push_at. rewrite !sepSPA. reflexivity.
  Qed.

  (* Frame rule for Hoare triples *)
  Lemma basic_frame R S P c Q :
    S |-- basic P c Q ->
    S |-- basic (P ** R) c (Q ** R).
  Proof. by rewrite <-spec_at_basic, <-spec_frame. Qed.

  (* Rule of consequence *)
  Lemma basic_roc P' Q' S P c Q:
    P |-- P' ->
    Q' |-- Q ->
    S |-- basic P' c Q' ->
    S |-- basic P c Q.
  Proof.
    move=> HP HQ H. rewrite /basic in H.
    setoid_rewrite <-HP in H. setoid_rewrite ->HQ in H. apply H.
  Qed.

  (* Morphisms for triples *)
  Global Instance basic_entails_m:
    Proper (lentails --> eq ==> lentails ++> lentails) basic.
  Proof.
    move => P P' HP c _ <- Q Q' HQ. apply: basic_roc; try eassumption.
    done.
  Qed.

  Global Instance basic_equiv_m:
    Proper (lequiv ==> eq ==> lequiv ==> lequiv) basic.
  Proof.
    move => P P' HP c _ <- Q Q' HQ. rewrite {1}/basic.
    setoid_rewrite HQ. setoid_rewrite HP. reflexivity.
  Qed.

  (* Special case of consequence for precondition *)
  Lemma basic_roc_pre P' S P c Q:
    P |-- P' ->
    S |-- basic P' c Q ->
    S |-- basic P c Q.
  Proof. move=> HP H. by rewrite ->HP. Qed.

  (* Special case of consequence for postcondition *)
  Lemma basic_roc_post Q' S P c Q:
    Q' |-- Q ->
    S |-- basic P c Q' ->
    S |-- basic P c Q.
  Proof. move=> HQ H. by rewrite <-HQ. Qed.

  Lemma basic_exists A S P c Q:
    (forall a:A, S |-- basic (P a) c Q) ->
    S |-- basic (lexists P) c Q.
  Proof. rewrite /basic => H. specintros => i j a. eforalls H. simple apply H. Qed.

  Global Instance AtEx_basic P c Q : AtEx (basic P c Q).
  Proof. rewrite /basic. apply _. Qed.

  Lemma basic_basic_context R S' P' Q' S P c Q:
    S' |-- basic P' c Q' ->
    S |-- S' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof. move=> Hc HS HP HQ. rewrite ->HS, ->HP, <-HQ. exact: basic_frame. Qed.

  (* Combine rule of consequence and frame *)
  Lemma basic_basic R P' Q' S P c Q:
    |-- basic P' c Q' ->
    P |-- P' ** R ->
    Q' ** R |-- Q ->
    S |-- basic P c Q.
  Proof.
    move=> Hc HP HQ. apply: basic_basic_context; try eassumption. done.
  Qed.
End Basic.

Hint Rewrite @spec_at_basic : push_at.

Hint Unfold basic : specapply.

Module Export Existentials_basic.
  Import Existentials.

  Lemma pq_basic {M} {HM: MemIs M} t c Q:
    match find t with
    | Some (mkf _ f) =>
        PullQuant (basic (eval t) c Q) (fun a => basic (f a) c Q)
    | None => True
    end.
  Proof.
    move: (@find_correct_pull t). case: (find t) => [[A f]|]; last done.
    red. move=> Heval. rewrite ->Heval.
    apply basic_exists => a. by apply lforallL with a.
  Qed.

  Hint Extern 0 (PullQuant (@basic ?M ?HM ?P ?c ?Q) _) =>
    let t := quote_term P in
    apply (@pq_basic M HM t c Q) : pullquant.

End Existentials_basic.
