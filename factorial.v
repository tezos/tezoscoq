From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

From Tezos
  Require Import language semantics.


Definition factorial_program :=
  (* stack state is given in the comments below *)
  (* [ n ] -- input parameter, n >= 0 *)
  DUP ;;
  (* [ n ; n ] *)
  EQ ;;
  (* [ (n = 0)? ; n ] *)
  IFB {{ DROP ;;
        (* [] *)
        PUSH (Int 1)
        (* [ 1 ] *) }}        (* return 0! = 1 *)
      {{ PUSH (Int 1) ;;    (* push accumulator's initial value *)
        (* [ acc ; n ] *)    (* acc = 1, n <> 0 *)
        SWAP ;;
        (* [ n ; acc ] *)
        DUP ;;
        (* [ n ; n ; acc ] *)
        NEQ ;;
        (* [ (n <> 0)? ; n; acc ] *)
        LOOP {{
          (* [ n ; acc ] *)
          DUP;;
          (* [ n ; n ; acc ] *)
          DIP {{ MUL }} ;;
          (* [ n ; n * acc ] *)
          PUSH (Int 1) ;;
          (* [ 1 ; n ; n * acc ] *)
          SWAP ;;
          (* [ n ; 1 ; n * acc ] *)
          SUB ;;
          (* [ n-1 ; n * acc ] *)
          DUP ;;
          (* [ n-1 ; n-1 ; n * acc ] *)
          NEQ
          (* [ (n-1 <> 0)? ; n-1 ; n * acc ] *)
        }} ;;
        (* [ 0 ; acc ] *)
        DROP
        (* [ acc ] *) }}.

Example typing_factorial :
  factorial_program :i: ([t_int] --> [t_int]).
Proof. by typecheck_program. Qed.


Lemma factorial_correct_eval m1 (n : nat) : evaluates (Some(factorial_program, [::Int (n%:Z)],m1)) (Some(Done,[::Int ((factorial n)%:Z)],m1)).
Proof.
do 4 apply: evaluates_onestep => /= .
apply: evaluates_if; case Hn : n => [|n1] //= .
- move => _.
  apply evaluates_onestep => /= .
  apply evaluates_onestep => /= .
  apply evaluates_onestep => /= .
  exact: evaluates_self.
- move => _.
  do 8 apply evaluates_onestep => /= .
  set body := (X in evaluates (Some(LOOP {{ X }} ;; _,_,_)) _) .
  have Hsuff b (z : int) zacc b1 :
      (z >= 1) ->
      b = get_neq (Int z) ->
      b1 = get_neq (Int (z-1)) ->
      evaluates ((Some(LOOP {{ body }},[:: b; Int z; Int zacc],m1))) (Some(LOOP {{body}},[:: b1 ; Int (z-1)%Z; Int (z*zacc)],m1)).
    move =>  H1 H2 H3.
    apply: evaluates_onestep => /= .
    have -> : b = DBool true.
      rewrite H2 /=; suff -> : z != 0; first by [].
      apply/negP; rewrite eq_sym => Hz0.
      by move/eqP in Hz0; rewrite -Hz0 in H1.
    do 14 apply: evaluates_onestep => /= .
    exists 0%N => /= .
    congr (Some _);congr(_,_,_);congr([::_;_;_]).
    by rewrite H3.
  apply: (@evaluates_seq _ _ _ _ _ ([::Int 0; Int ((n1.+1)`!)%:Z])); last first => // .
    by apply: evaluates_onestep => /= ; exists 0%N.
  (* Generalize the goal a little bit. *)
  suff {Hn n1} H  : (forall N acc, acc * (Posz (factorial n)) = factorial N ->
    evaluates (Some (LOOP {{body}}, [:: get_neq (Int n); Int n; Int acc], m1))
      (Some (Done(*Nop*), [:: Int 0; Int N`!], m1))).
    specialize (H n 1).
    replace (DBool true) with (get_neq (Int n)) by by subst.
    rewrite -Hn; apply: H; apply: mul1r.
  elim: n => [|n0 HIn] N acc H.
    by apply: evaluates_onestep => /= ; rewrite -H fact0 mulr1; exact: evaluates_self.
  apply: (@evaluates_trans _ (Some(_,[::_;_;_],_))); first exact: Hsuff.
  specialize (HIn N (Posz n0.+1 * acc)).
  have -> : (Posz n0.+1 - 1) = (Posz n0) by rewrite intS -addrAC subrr add0r.
  by apply: HIn; rewrite -H factS PoszM mulrCA mulrA.
Qed.


(* tests for factorial *)
(* Variable m : memory. *)

(* Eval native_compute in evaluate 1000 (Some(factorial_program,[::Int 6],m)). *)
(* Eval native_compute in evaluate_trace (Some(factorial_program,[::Int 5],m)) 100. *)