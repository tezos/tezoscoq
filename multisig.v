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
  Require Import language blockchain semantics.

(* Original Michelson program:
storage (pair (map string key) uint8) ;
return unit ;
parameter (pair (pair (contract unit unit) tez) (map string signature)) ;
code
  {
    # storage is a pair of
    #     map from names to public and
    #     number of valid signatures required
    # parameter is a
    # pair
    #    pair $destination $amount (where to send the funds and how much)
    #    map from names to signature (the actual signatures)
    DUP ; DUP; CDR; SWAP; CADR; DIP { DUP } ;  # $input : $storage : $storage
    DIP { CDR; SWAP; CAR } ;             # $input : $keys : $N : $storage
    DUP; CDR; SWAP; CAR ;                # $action : $signatures : $keys : $N: $storage
    DUP; H ;                             # $hash : $action : $signatures : $keys : $N: $storage
    DUUUUUUP; CDAR ; PAIR ;                        # pair $keys $hash : $action : $signatures : $N: $storage
    PUSH uint8 0; SWAP; PAIR ;           # pair (pair $keys $hash) 0 : $action : $signatures : $N : $storage
    DIP { SWAP }; SWAP ;                 # $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage
    LAMBDA (pair (pair string signature) (pair (pair (map string key) string) uint8)) (pair (pair (map string key) string) uint8)
     {# S = pair (pair $name $signature) (pair (pair $keys $hash) $counter)
      DUP; CDR; SWAP; CAR ;
      # S = pair $name $signature : pair (pair $keys $hash) $counter
      DUP; CDR; SWAP; CAR ;
      # S = $name : $signature : pair (pair $keys $hash) $counter
      DIIP { DUP; CDR; SWAP; CAR } ;
      # S = $name : $signature : (pair $keys $hash) : $counter
      DIIP { DUP; CDR; SWAP; CAR }; SWAP ;
      # S = $signature : $name : $keys : $hash : $counter
      DIP
        { DIP { DUP }; GET ; # attempt to get the key for a given user
          IF_NONE { FAIL } { } # fail for unknown signer, otherwise key is pushed on the stack
        };
      # S = $signature : $key : $keys : $hash : $counter
      DIIP  { SWAP ; DUP } ;
      # S = $signature : $key : $hash : $hash : $keys : $counter
      DIIIP { SWAP; PAIR; SWAP } ;
      # S = $signature : $key : $hash : $counter: pair $keys $hash
      SWAP ; DIP { PAIR } ;
      # S = $signature : pair $key $hash : $counter: pair $keys $hash
      CHECK_SIGNATURE ;
      # S = $sig_valid? : $counter : pair $keys $hash
      IF { PUSH uint8 1; CHECKED_ADD } { FAIL } ; # we don't *have* to fail on an invalid signature, but it is good hygiene
      # S = $counter : pair $keys $hash
      SWAP; PAIR ;
      # S = pair (pair $keys hash) $counter
     } ;
    # S = $reducer : $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage
    REDUCE ; # this is where the counting happens
    # S = pair (pair $keys $hash) $counter : $action : $N : $storage
    CDR ; DIP { SWAP ; DROP ; SWAP } ;
    # S = $counter : $N : $action : $storage
    IFCMPGE
      { # if we have enough signatures
        DUP ; CDR ; SWAP ; CAR ; UNIT ; DIP { SWAP } ; DIIIP { CDR } ;
        # unit : $amount : $contract : $storage
        TRANSFER_TOKENS;
        DROP ; UNIT ; PAIR
      }
      {
        FAIL
      } # not enough signatures, fail
  }
*)

(* Coq version, with some differences:
    - double all the ';', '{' and '}'
    - remove trailing ;;
    - fill empty {{ }} with a NOP
    - replace H by HASH
    - remove type annotations from LAMBDA and PUSH, but add a type
      constructor to PUSH
    - expand REDUCE to be the correct one
*)
Definition multisig_prog :=
    (*  storage is a pair of *)
    (*      map from names to public and *)
    (*      number of valid signatures required *)
    (*  parameter is a *)
    (*  pair *)
    (*     pair $destination $amount (where to send the funds and how much) *)
    (*     map from names to signature (the actual signatures) *)
    DUP ;; DUP;; CDR;; SWAP;; CADR;; DIP {{ DUP }} ;;  (*  $input : $storage : $storage *)
    DIP {{ CDR;; SWAP;; CAR }} ;;             (*  $input : $keys : $N : $storage *)
    DUP;; CDR;; SWAP;; CAR ;;                (*  $action : $signatures : $keys : $N: $storage *)
    DUP;; HASH ;;                             (*  $hash : $action : $signatures : $keys : $N: $storage *)
    DUUUUUUP;; CDAR ;; PAIR ;;                        (*  pair $keys $hash : $action : $signatures : $N: $storage *)
    PUSH (Int 0);; SWAP;; PAIR ;;           (*  pair (pair $keys $hash) 0 : $action : $signatures : $N : $storage *)
    DIP {{ SWAP }};; SWAP ;;                 (*  $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage *)
    LAMBDA (* (pair (pair string signature) (pair (pair (map string key) string) uint8)) (pair (pair (map string key) string) uint8) *)
     {{(*  S = pair (pair $name $signature) (pair (pair $keys $hash) $counter) *)
      DUP;; CDR;; SWAP;; CAR ;;
      (*  S = pair $name $signature : pair (pair $keys $hash) $counter *)
      DUP;; CDR;; SWAP;; CAR ;;
      (*  S = $name : $signature : pair (pair $keys $hash) $counter *)
      DIIP {{ DUP;; CDR;; SWAP;; CAR }} ;;
      (*  S = $name : $signature : (pair $keys $hash) : $counter *)
      DIIP {{ DUP;; CDR;; SWAP;; CAR }};; SWAP ;;
      (*  S = $signature : $name : $keys : $hash : $counter *)
      DIP
        {{ DIP {{ DUP }};; GET ;; (*  attempt to get the key for a given user *)
          IF_NONE {{ FAIL }} {{ NOP }} (*  fail for unknown signer, otherwise key is pushed on the stack *)
        }};;
      (*  S = $signature : $key : $keys : $hash : $counter *)
      DIIP  {{ SWAP ;; DUP }} ;;
      (*  S = $signature : $key : $hash : $hash : $keys : $counter *)
      DIIIP {{ SWAP;; PAIR;; SWAP }} ;;
      (*  S = $signature : $key : $hash : $counter: pair $keys $hash *)
      SWAP ;; DIP {{ PAIR }} ;;
      (*  S = $signature : pair $key $hash : $counter: pair $keys $hash *)
      CHECK_SIGNATURE ;;
      (*  S = $sig_valid? : $counter : pair $keys $hash *)
      IFB {{ PUSH (Int 1);; ADD }} {{ FAIL }} ;; (*  we don't *have* to fail on an invalid signature, but it is good hygiene *)
      (*  S = $counter : pair $keys $hash *)
      SWAP;; PAIR
      (*  S = pair (pair $keys hash) $counter *)
     }} ;;
    (*  S = $reducer : $signatures : pair (pair $keys $hash) 0  : $action : $N : $storage *)
    MAP_REDUCE ;; (*  this is where the counting happens *)
    (*  S = pair (pair $keys $hash) $counter : $action : $N : $storage *)
    CDR ;; DIP {{ SWAP ;; DROP ;; SWAP }} ;;
    (*  S = $counter : $N : $action : $storage *)
    IFCMPGE
      {{ (*  if we have enough signatures *)
        DUP ;; CDR ;; SWAP ;; CAR ;; PUSH Unit ;; DIP {{ SWAP }} ;; DIIIP {{ CDR }} ;;
        (*  unit : $amount : $contract : $storage *)
        TRANSFER_TOKENS;;
        DROP ;; UNIT ;; PAIR
      }}
      {{
        FAIL
      }} (*  not enough signatures, fail *)
.

(* Typing. *)

Definition multisig_storage_type : type := t_pair (t_map t_string t_key) t_int.
Definition multisig_param_type : type := t_pair (t_pair (t_contract t_unit t_unit)
  t_tez) (t_map t_string t_signature).

Definition multisig_type : instr_type := [
  t_pair (t_pair t_tez multisig_param_type) multisig_storage_type
  ] --> [ t_pair t_unit multisig_storage_type ].

Theorem multisig_typed : multisig_prog :i: multisig_type.
Proof. typecheck_program. Qed.

(* Parameters for interpreting the contract (some are arbitrary) *)

Definition sender_handle := 0%nat.
Definition receiver_handle := 1%nat.

(* sender contract *)
Definition sender_contract : contract := C (K "sender") None false false FAIL.
Definition sender_balance : balance := Tez 10.
Definition sender_storage : storage := Unit.
Definition sender_contract_repr := (sender_contract,sender_balance,sender_storage).

(* receiver contract *)
Definition receiver_contract : contract := C (K "receiver") None false false FAIL.
Definition receiver_balance : balance := Tez 0.
Definition receiver_storage : storage := Unit.
Definition receiver_contract_repr := (receiver_contract,receiver_balance,receiver_storage).


Definition m :=
  checked_put eqkey receiver_handle receiver_contract_repr
  (checked_put eqkey sender_handle sender_contract_repr empty_blockchain).

(* state of the blockchain before executing multisig *)
Eval vm_compute in m.

Definition void_contract_argument := DContract receiver_handle.
Definition multisig_transfer_amount := DTez (Tez 1).
Definition text_to_sign := get_raw_hash (DPair (DContract receiver_handle) (multisig_transfer_amount)).
Definition input_signatures :=
  DMap
    [(DString (Sstring "Satoshi"),
      DSignature (Sign (K "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa") text_to_sign));

      (DString (Sstring "Wikileaks"),
       DSignature (Sign (K "1HB5XMLmzFVj8ALj6mfBsbifRoD4miY36v") text_to_sign))].

Definition argument :=
  DPair
    (DPair
       void_contract_argument
       multisig_transfer_amount)
    input_signatures.

(* the list of public keys controlling the smart contract *)
Definition raw_storage_map : myMap tagged_data tagged_data :=
  [
    (DString (Sstring "Satoshi"),DKey (K "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa"));
    (DString (Sstring "Laszlo"),DKey (K "1XPTgDRhN8RFnzniWCddobD9iKZatrvH4"));
    (DString (Sstring "Wikileaks"),DKey (K "1HB5XMLmzFVj8ALj6mfBsbifRoD4miY36v"))].
Definition storage_map := DMap raw_storage_map.
Definition needed_votes := Int 2.

Definition storage := DPair storage_map needed_votes.
Definition amount := DTez (Tez 42).

Eval vm_compute in evaluate sender_handle 287 (Some(multisig_prog,[::DPair (DPair amount argument) storage],m)).



Section Spec.

(* stub of specification for multisig *)
Lemma multisig_spec hsender hreceiver (b : blockchain) amount storage_map input_signatures_map multisig_transfer_amount needed_votes :
  let void_contract_argument := DContract hreceiver in
  let argument := DPair (DPair void_contract_argument multisig_transfer_amount) (DMap input_signatures_map) in
  let storage :=  DPair storage_map needed_votes in
  evaluates
    hsender
    (Some (multisig_prog,[::DPair (DPair amount argument) storage],b))
    (Some(Done,nil,empty_blockchain)).
Proof.
do 70! (apply: evaluates_onestep) => /= .
Abort.
