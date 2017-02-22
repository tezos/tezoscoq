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

(* tests for notation precedence levels and associativity *)
Section NotationTests.

(* TODO: we might need to move this somewhere else and add some tests when we introduce notation for typing, etc. *)

Goal
  (DROP ;; DROP ;; NOP) =
  Seq Drop (Seq Drop Nop). done. Qed.

Goal
  (PUSH (DBool true) ;; IFB {{ NOP ;; NOP }} {{ NOP }}) =
  (Seq (Push (DBool true)) (If (Seq Nop Nop) Nop)). done. Qed.

End NotationTests.


Section Typechecking_Tests.

(* tests *)
Example typing_drop1 t1 :
  DROP :i: ([t1] --> []).
Proof. by typecheck_program. Qed.

Example typing_drop2 t1 t2 :
  (DROP ;; DROP) :i: ([t1 ; t2] --> []).
Proof. by typecheck_program. Qed.

Example typing_drop3 t1 t2 t3 :
  (DROP ;; DROP ;; DROP) :i: ([t1 ; t2 ; t3] --> []).
Proof. by typecheck_program. Qed.

Example typing_drop4 t1 t2 t3 t4 :
  (DROP ;; DROP ;; DROP ;; DROP) :i: ([t1 ; t2 ; t3 ; t4] --> []).
Proof. by typecheck_program. Qed.

Example typing_push_drop1 :
  (PUSH (Int 0) ;; DROP) :i: ([] --> []).
Proof. by typecheck_program. Qed.

Example typing_push_drop2 :
  (DUP ;;
   EQ ;;
   IFB {{ DROP ;; PUSH (Int 0) }}
       {{ DROP ;; PUSH (Int 0) }})
  :i: ([t_int] --> [t_int]).
Proof. by typecheck_program. Qed.

(* TODO: add some more tests for typechecking *)

(* XXX: variadic functions are not allowed! (i.e. a program which empties its input stack must not typecheck!)
*)

End Typechecking_Tests.

Section EvaluationTests.

Variable m : memory.

Eval vm_compute in step_fun (DROP ;; DROP) [::Int 1;Int 1] m.
Eval vm_compute in step_fun (NOP ;; DROP) [::Int 1] m.
Eval vm_compute in evaluate 1 (Some(DROP,[::Int 1; Int 1],m)).
Eval vm_compute in evaluate 100 (Some((DROP ;; DROP),[::Int 1;Int 1],m)).

End EvaluationTests.
