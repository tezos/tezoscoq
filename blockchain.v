From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

From Tezos
  Require Import language.

(* Abstraction of the Tezos state, from page 8 of paper *)

Inductive contract := C : key -> option key ->
              (* spendable *) bool -> (* delegatable *) bool ->
              instr -> contract.
(* saved for serializing later *)
(* | DContract (K k) ok sp dl am instr => "<Contract : key = " ++ k ++ "; code = " ++ "<code>" ++ ">" *)
Definition balance := tez.
Definition storage := tagged_data.

Definition contract_repr := (contract * balance * storage)%type.

Definition dummy_contract : contract := C (K "dummy") None false false FAIL.
Definition dummy_balance : balance := Tez 0.
Definition dummy_storage : storage := Unit.

Definition dummy_contract_repr := (dummy_contract,dummy_balance,dummy_storage).

Definition blockchain := myMap handle contract_repr.

Definition empty_blockchain : blockchain := nil.

Definition max_handle (b : blockchain) : option handle := if b is nil then None else Some (foldl (fun x y => maxn x y.1) 0 b).

Definition get_new_handle (b : blockchain) :=
  match max_handle b with
    | None => 0
    | Some h => h.+1 end.

Definition eqkey (x y : nat) := x == y.

Definition get_contract (h : handle) (b : blockchain) : option contract_repr :=
  get eqkey h 0 (dummy_contract_repr) b.

Definition create_contract (k : key) (ok : option key) (sp dl : bool) (am : tez) (i : instr) (storage : tagged_data) (b : blockchain) : handle * blockchain :=
  let h := get_new_handle b in
  let contract := C k ok sp dl i in
  (h,put h (contract,am,storage) b).

Definition transfer_tokens
           (input : tagged_data) (amount : tez) (hsender hreceiver : handle)
           (new_storage : tagged_data) (b : blockchain) :
  option (tagged_data * blockchain) :=
  match get_contract hreceiver b with
    | None => None
    | Some(rcontract,rbalance,rstorage) =>
      match get_contract hsender b with
        | None => (* the sender does not exist *) None
        | Some(scontract,sbalance,sstorage) =>
          match amount,sbalance,rbalance with
            | Tez amount,Tez sbalance,Tez rbalance =>
              if (amount <= sbalance) then
                let b' :=
                    checked_put eqkey hsender (scontract,Tez (sbalance-amount),sstorage) b in
                let b'' :=
                    checked_put eqkey hreceiver (rcontract,Tez(rbalance+amount),rstorage) b' in
                Some (Unit,b'')
              else
                None
          end
      end
  end.
          (* Definition checked_put {A} {B} eq (k : A) (v : B) m := *)
  (* (k,v)::(remove eq k v m). *)