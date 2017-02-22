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

Definition multisig_prog :=
(* e storage (pair (map string key) uint8) *)
(* return void *)
(* parameter (pair (pair (contract void void) tez) (map string signature) ) *)
(* code *)

    (* # storage is a pair of *)
    (* #     map from names to public and *)
    (* #     number of valid signatures required *)
    (* # parameter is a *)
    (* # pair *)
    (* #    pair $destination $amount (where to send the funds and how much) *)
    (* #    map from names to signature (the actual signatures) *)
    DUP;; CDR;; SWAP;; CADR;; DIP {{ DUP }} ;;  (* $input : $storage : $storage *)
    DIP {{ CDR;; SWAP;; CAR }} ;;             (* $input : $keys : $N : $storage *)
    DUP;; CDR;; SWAP;; CAR ;;                (* $action : $signatures : $keys : $N: $storage *)
    DUP;; HASH ;;                             (* $hash : $action : $signatures : $keys : $N: $storage *)
    (* DIP {{ DIP {{ DIP {{ DUP }} ;; SWAP }} ;; SWAP }} ;; SWAP *)
    DUPn 3;; PAIR ;;                         (* pair $keys $hash : $action : $signatures : $N: $storage *)
    PUSH (Int 0);; SWAP;; PAIR ;;           (* pair (pair $keys $hash) 0 : $action : $signatures : $N : $storage *)
    DIP {{ SWAP }};; SWAP ;;                 (* $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage *)
    LAMBDA (* (pair (pair string signature) (pair (pair (map string key) string) uint8)) (pair (pair (map string key) string) uint8) *) {{
      (* S = pair (pair $name $signature) (pair (pair $keys $hash) $counter) *)
      DUP;; CDR;; SWAP;; CAR ;;
      (* S = pair $name $signature : pair (pair $keys $hash) $counter *)
      DUP;; CDR;; SWAP;; CAR ;;
      (* S = $name : $signature : pair (pair $keys $hash) $counter *)
      DIIP {{ DUP;; CDR;; SWAP;; CAR }} ;;
      (* S = $name : $signature : (pair $keys $hash) : $counter *)
      DIIP {{ DUP;; CDR;; SWAP;; CAR }};; SWAP ;;
      (* S = $signature : $name : $keys : $hash : $counter *)
      DIP {{
        DIP {{ DUP }};; GET ;; (* attempt to get the key for a given user *)
        IF_SOME {{ NOP }} {{ FAIL }} (* fail for unknown signer, otherwise key is pushed on the stack *)
      }};;
      (* S = $signature : $key : $keys : $hash : $counter *)
      DIIP  {{ SWAP ;; DUP }} ;;
      (* S = $signature : $key : $hash : $hash : $keys : $counter *)
      DIIIP {{ SWAP;; PAIR;; SWAP }} ;;
      (* S = $signature : $key : $hash : $counter: pair $keys $hash *)
      DIP {{ PAIR }} ;;
      (* S = $signature : pair $key $hash : $counter: pair $keys $hash *)
      CHECK_SIGNATURE ;;
      (* S = $sig_valid? : $counter : pair $keys $hash *)
      IFB {{ PUSH (Int 1);; ADD }} {{ FAIL }} ;; (* we don't *have* to fail on an invalid signature, but it is good hygiene *)
      (* S = $counter : pair $keys $hash *)
      SWAP;; PAIR
      (* S = pair (pair $keys hash) $counter *)
    }} ;;
    (* S = $reducer : $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage *)
    MAP_REDUCE ;; (* this is where the counting happens *)
    (* S = pair (pair $keys $hash) $counter : $action : $N : $storage *)
    CDR;; DIP {{ SWAP }} ;;
    (* S = $counter : $N : $action : $storage *)
    IFCMPGE {{ (* if we have enough signatures *)
      DUP;; CDR;; SWAP;; CAR;; PUSH Void;;
      (* void : $amount : $contract : $storage  *)
      TRANSFER_FUNDS;; DROP
    }}
    {{
      FAIL
    }} (* not enough signatures, fail *)
.

Variable m : memory.



(* dixit @klapklok *)
(* So, the calling convention for contracts is to receive a stack with a single element (pair (pair amount arg) storage) *)
(* and to return a stack with a single element (pair return storage) *)

(* (pair (pair (contract void void) tez) (map string signature) ) *)
Definition argument := DPair (DPair (Int 6) (DTez (Tez 1))) (DMap empty_map).
Definition storage := DPair (DMap empty_map) (Int 0).
Definition amount := DTez (Tez 42).

Eval native_compute in evaluate 55 (Some(multisig_prog,[::DPair (DPair amount argument) storage],m)).
