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

(* 287 *)
Eval vm_compute in m.
Eval vm_compute in evaluate sender_handle 287 (Some(multisig_prog,[::DPair (DPair amount argument) storage],m)).



Section Spec.

(* Definition Dproj1 A B (t : tagged_data) (H : t :d: t_pair A B) : tagged_data. *)
(* inversion H. *)
(* exact: a. *)
(* Defined. *)

(* Lemma Dproj1_typed A B t (H : t :d: t_pair A B) : @Dproj1 A B t H :d: A. *)
(* case: t H => // . *)


(* stub of specification for multisig *)
Lemma multisig_correct hsender hreceiver (b b' : blockchain) amount storage_map input_signatures_map multisig_transfer_amount needed_votes :
  let void_contract_argument := DContract hreceiver in
  let action := (DPair void_contract_argument multisig_transfer_amount) in
  let argument := DPair action (DMap input_signatures_map) in
  let storage :=  DPair storage_map (Int needed_votes) in
  (* begin preconditions *)
  multisig_transfer_amount :d: t_tez ->
  void_contract_argument :d: (t_contract t_unit t_unit) ->
  needed_votes <= size input_signatures_map ->
(* subgoal 2 (ID 43479) is: *)

(* subgoal 3 (ID 43276) is: *)
(*  needed_votes :d: t_int *)
  storage_map :d: t_map t_string t_key ->
  well_typed_map t_string t_signature input_signatures_map ->
  (* end preconditions *)
  evaluates
    hsender
    (Some (multisig_prog,[::DPair (DPair amount argument) storage],b))
    (Some(Done,nil,b')).
Proof.
move => void_contract_argument action argument storage typed_amount typed_contract Hineq t_storage t_Map.
do 70! (apply: evaluates_onestep) => /= .
apply: evaluates_trans.
apply: evaluates_weaken.
set lambda := (X in DLambda X).
have Hlamtype : lambda :i: ([(t_pair (t_pair t_string t_signature) (t_pair (t_pair (t_map t_string t_key) t_string) t_int))] -->  [(t_pair (t_pair (t_map t_string t_key) t_string) t_int)])%type.
by typecheck_program.

(* x has type (pair (pair (map string key) string) uint8) *)

apply (@evaluates_map_reduce_usable
          (fun x kv =>
             let key := kv.1 in
             match x with
               | DPair (DPair (DMap map1) (DString s)) (Int counter) =>
                 match get (fun x y => eq_td x y) key Unit Unit map1 with
                   | Some (DKey key0) =>
                     match kv.2 with
                       | DSignature sig =>
                         if check_signature key0 sig s then
                           Some (DPair (DPair (DMap map1) (DString s)) (Int (1 + counter)))
                         else
                           None
                       | _ => None
                     end
                   | _ => None end
               | _ => None end) _ _ _ (t_pair (t_pair (t_map t_string t_key) t_string) t_int) t_string t_signature).
  - by typecheck_program.
  - constructor; constructor.
      exact: t_storage.
  - by constructor.
  - exact: t_Map.
  - move => x key val Hx Hkey Hval.
    case: x Hx => // [x1 counter] Htypex .
    inversion Htypex.
    case: x1 Htypex X H0 => // .
    intros => /= .
    (* case: counter Htypex X0 H1 => //; intros.   *)
    case: t X H0 Htypex => // [map1] Hmap1 Heq.
    case t0 => // ; intros.
    case counter => //; intros.
    case get => // ; intros.
    case t => //; intros.
    inversion Hval.
    case Hcheck: check_signature => // .
    constructor; constructor => // .
    by inversion Htypex; inversion X.
  - intros.
    case x => //; intros.
    case t => //; intros.
    case t1 => //; intros.
    case t2 => //; intros.
    case t0 => //; intros.
    rewrite /=.
    case Hget: (get (fun x0 : tagged_data => [eta eq_td x0]) key Unit Unit m0) => // [a].
    case Ha : a => // [k]  ; intros.
    case val => // ; intros.
    case checksig : (check_signature k s0 s) => // .
    do 41 (apply: evaluates_onestep => /= ).
    apply: evaluates_onestep => /= .
    rewrite Hget.
    do 25 apply: evaluates_onestep => /= .
    (* have Hakey : a :d: t_key by rewrite Ha; case k; constructor. *)
    rewrite Ha.
    apply: evaluates_onestep => /= .
    rewrite checksig.
    do 9 apply: evaluates_onestep => /= .
    exact: evaluates_self.
    (* have Ha : a :d: t_key by admit. *) (* we can't possibly know that yet because it depends on the map m0 being well typed and on a lemma on get's output type.. *)

instantiate (1 := DPair (DPair storage_map (get_hash action)) (Int (size input_signatures_map)%:Z)).
admit.

(* suff Hineq : (needed_votes <= size input_signatures_map). *)
do 10 apply: evaluates_onestep => /= .
apply: evaluates_onestep => /= .
set i := (X in Int X).
have Hi : 0 <= i.
  rewrite ler_eqVlt in Hineq.
  case/orP: Hineq.
    by move/eqP; rewrite /i => ->; rewrite eq_refl // .
  admit.
apply: evaluates_onestep => /= .
apply: evaluates_onestep => /= ; rewrite Hi.
do 20 apply: evaluates_onestep => /= .

inversion typed_amount.
apply: evaluates_onestep => /= .
admit.
Admitted.

End Spec.
