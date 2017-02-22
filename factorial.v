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
  Require Import language.


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