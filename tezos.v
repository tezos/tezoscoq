Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrnat.
Require Import ZArith.
Require Import String.

Section Grammar.

    (* <tagged data> ::= *)
    (*   | Int8 <int constant> *)
    (*   | Int16 <int constant> *)
    (*   | Int32 <int constant> *)
    (*   | Int64 <int constant> *)
    (*   | Uint8 <int constant> *)
    (*   | Uint16 <int constant> *)
    (*   | Uint32 <int constant> *)
    (*   | Uint64 <int constant> *)
    (*   | Void *)
    (*   | True *)
    (*   | False *)
    (*   | <string constant> *)
    (*   | <float constant> *)
    (*   | Timestamp <timestamp constant> *)
    (*   | Signature <signature constant> *)
    (*   | Tez <tez constant> *)
    (*   | Key <key constant> *)
    (*   | Left <tagged data> <type> *)
    (*   | Right <type> <tagged data> *)
    (*   | Or <type> <type> <untagged data> *)
    (*   | Ref <tagged data> *)
    (*   | Ref <type> <untagged data> *)
    (*   | Some <tagged data> *)
    (*   | Some <type> <untagged data> *)
    (*   | None <type> *)
    (*   | Option <type> <untagged data> *)
    (*   | Pair <tagged data> <tagged data> *)
    (*   | Pair <type> <type> <untagged data> <untagged data> *)
    (*   | List <type> <untagged data> ... *)
    (*   | Set <comparable type> <untagged data> ... *)
    (*   | Map <comparable type> <type> (Item <untagged data> <untagged data>) ... *)
    (*   | Contract <type> <type> <contract constant> *)
    (*   | Lambda <type> <type> { <instruction> ... } *)

Inductive tez := Tez : nat -> tez. 

Inductive tagged_data:=
      | Int8 : Z -> tagged_data
      | Int16 : Z -> tagged_data
      | Int32 : Z -> tagged_data
      | Int64 : Z -> tagged_data
      | Uint8 : Z -> tagged_data
      | Uint16 : Z -> tagged_data
      | Uint32 : Z -> tagged_data
      | Uint64 : Z -> tagged_data
      | Void
      | Dtrue
      | Dfalse
      | DString : string -> tagged_data
      (* | <float constant> *)
      (* | Timestamp <timestamp constant> *)
      (* | Signature <signature constant> *)
      | DTez : tez -> tagged_data.
      (* | Key <key constant> *)
      (* | Left <tagged data> <type> *)
      (* | Right <type> <tagged data> *)
      (* | Or <type> <type> <untagged data> *)
      (* | Ref <tagged data> *)
      (* | Ref <type> <untagged data> *)
      (* | Some <tagged data> *)
      (* | Some <type> <untagged data> *)
      (* | None <type> *)
      (* | Option <type> <untagged data> *)
      (* | Pair <tagged data> <tagged data> *)
      (* | Pair <type> <type> <untagged data> <untagged data> *)
      (* | List <type> <untagged data> ... *)
      (* | Set <comparable type> <untagged data> ... *)
      (* | Map <comparable type> <type> (Item <untagged data> <untagged data>) ... *)
      (* | Contract <type> <type> <contract constant> *)
      (* | Lambda <type> <type> { <instruction> ... } *)


    (* <untagged data> ::= *)
    (*   | <int constant> *)
    (*   | <string constant> *)
    (*   | <float constant> *)
    (*   | <timestamp constant> *)
    (*   | <signature constant> *)
    (*   | <key constant> *)
    (*   | <tez constant> *)
    (*   | <contract constant> *)
    (*   | Void *)
    (*   | True *)
    (*   | False *)
    (*   | Pair <untagged data> <untagged data> *)
    (*   | Left <untagged data> *)
    (*   | Right <untagged data> *)
    (*   | Ref <untagged data> *)
    (*   | Some <untagged data> *)
    (*   | None *)
    (*   | List <untagged data> ... *)
    (*   | Set <untagged data> ... *)
    (*   | Map (Item <untagged data> <untagged data>) ... *)



    (* <instruction> ::= *)
    (*   | { <instruction> ... } *)
    (*   | DROP *)
    (*   | DUP *)
    (*   | SWAP *)
    (*   | PUSH <tagged data> *)
    (*   | SOME *)
    (*   | NONE <type> *)
    (*   | IF_NONE { <instruction> ... } { <instruction> ... } *)
    (*   | PAIR *)
    (*   | CAR *)
    (*   | CDR *)
    (*   | LEFT <type> *)
    (*   | RIGHT <type> *)
    (*   | IF_LEFT { <instruction> ... } { <instruction> ... } *)
    (*   | NIL <type> *)
    (*   | CONS *)
    (*   | IF_CONS { <instruction> ... } { <instruction> ... } *)
    (*   | EMPTY_SET <type> *)
    (*   | EMPTY_MAP <comparable type> <type> *)
    (*   | ITER *)
    (*   | MAP *)
    (*   | REDUCE *)
    (*   | MEM *)
    (*   | GET *)
    (*   | UPDATE *)
    (*   | REF *)
    (*   | DEREF *)
    (*   | SET *)
    (*   | IF { <instruction> ... } { <instruction> ... } *)
    (*   | LOOP { <instruction> ... } *)
    (*   | LAMBDA <type> <type> { <instruction> ... } *)
    (*   | EXEC *)
    (*   | DIP { <instruction> ... } *)
    (*   | FAIL *)
    (*   | NOP *)
    (*   | CONCAT *)
    (*   | ADD *)
    (*   | SUB *)
    (*   | MUL *)
    (*   | DIV *)
    (*   | ABS *)
    (*   | NEG *)
    (*   | MOD *)
    (*   | LSL *)
    (*   | LSR *)
    (*   | OR *)
    (*   | AND *)
    (*   | XOR *)
    (*   | NOT *)
    (*   | COMPARE *)
    (*   | EQ *)
    (*   | NEQ *)
    (*   | LT *)
    (*   | GT *)
    (*   | LE *)
    (*   | GE *)
    (*   | CAST *)
    (*   | CHECKED_ABS *)
    (*   | CHECKED_NEG *)
    (*   | CHECKED_ADD *)
    (*   | CHECKED_SUB *)
    (*   | CHECKED_MUL *)
    (*   | CHECKED_CAST *)
    (*   | FLOOR *)
    (*   | CEIL *)
    (*   | INF *)
    (*   | NAN *)
    (*   | ISNAN *)
    (*   | NANAN *)
    (*   | MANAGER *)
    (*   | TRANSFER_FUNDS *)
    (*   | CREATE_ACCOUNT *)
    (*   | CREATE_CONTRACT *)
    (*   | NOW *)
    (*   | AMOUNT *)
    (*   | BALANCE *)
    (*   | CHECK_SIGNATURE *)
    (*   | H *)
    (*   | STEPS_TO_QUOTA *)
    (*   | SOURCE <type> <type> *)

Definition stack := list tagged_data.

Inductive instruction :=
      | TransferFunds : instruction
      | Balance : instruction.
    
(* <type> ::= *)
(*       | int8 *)
(*       | int16 *)
(*       | int32 *)
(*       | int64 *)
(*       | uint8 *)
(*       | uint16 *)
(*       | uint32 *)
(*       | uint64 *)
(*       | void *)
(*       | string *)
(*       | float *)
(*       | tez *)
(*       | bool *)
(*       | key *)
(*       | timestamp *)
(*       | signature *)
(*       | ref <type> *)
(*       | option <type> *)
(*       | list <type> *)
(*       | set <comparable type> *)
(*       | contract <type> <type> *)
(*       | pair <type> <type> *)
(*       | union <type> <type> *)
(*       | lambda <type> <type> *)
(*       | map <comparable type> <type> *)

Inductive type :=
| void : type
| ttez : tez -> type
| tcontract : type -> type -> type.

    (* <comparable type> ::= *)
    (*   | int8 *)
    (*   | int16 *)
    (*   | int32 *)
    (*   | int64 *)
    (*   | uint8 *)
    (*   | uint16 *)
    (*   | uint32 *)
    (*   | uint64 *)
    (*   | string *)
    (*   | float *)
    (*   | tez *)
    (*   | bool *)
    (*   | key *)
    (*   | timestamp *)

End Grammar.

Section Semantics.

(* To be changed once we know what we want *)
Variables memory : Type.

End Semantics.