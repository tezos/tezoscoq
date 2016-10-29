From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool ssrnat seq.
From Coq
  Require Import ZArith String List.
Import ListNotations.

Set Implicit Arguments.

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


Section Instructions.

(* In what follows, the "nested inductive types" approach calls for a custom (user-defined) induction principle *)

(* XXX: should we use a notation for `list instr` here? *)
Inductive instr :=
| Drop : instr
| If : list instr -> list instr -> instr
| Loop : list instr -> instr.

Definition instructions := list instr.

(* The custom induction principle for the `instr` datatype.
 *  We need it because the autogenerated `instr_ind` is too
 * weak for proofs.
 * Based on the approach described in
 * "Certified Programming with Dependent Types" book by A. Chlipala:
 * http://adam.chlipala.net/cpdt/html/InductiveTypes.html#lab32
 *)
Variable P : instr -> Prop.
Hypothesis Drop_case : P Drop.
Hypothesis If_case : forall ins1 ins2 : instructions,
    Forall P ins1 -> Forall P ins2 -> P (If ins1 ins2).
Hypothesis Loop_case : forall ins : instructions,
    Forall P ins -> P (Loop ins).
Fixpoint instr_ind' (i : instr) : P i :=
  let list_instr_ind :=
      (fix list_instr_ind (ins : instructions) : Forall P ins :=
         match ins with
         | [] => Forall_nil _
         | i' :: ins' => Forall_cons _ (instr_ind' i') (list_instr_ind ins')
         end) in
  match i with
    | Drop => Drop_case
    | If ins1 ins2 => If_case (list_instr_ind ins1) (list_instr_ind ins2)
    | Loop ins => Loop_case (list_instr_ind ins)
    end.
End Instructions.

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

Section Semantics.

(* To be changed once we know what we want *)
Variables memory : Type.

(* until we get a better sense of what works best, we will try two
ways to do the small steps semantics: one with an inductive type of
reduction rules, and one with a step function. *)

(* First version: inductive semantics *)
Section Ind_semantics.

Inductive step : instr * instructions * stack * memory ->
                 instructions * stack * memory -> Prop :=
| stepDrop : forall ins x s m, step (Drop, ins, x::s, m)
                               (ins, s, m)
| stepIfTrue : forall cont insT insF s m,
    step (If insT insF, cont, Dtrue :: s, m)
         (insT ++ cont, s, m)
| stepIfFalse : forall cont insT insF s m,
    step (If insT insF, cont, Dfalse :: s, m)
         (insF ++ cont, s, m)
| stepLoopGo : forall cont body s m,
    step (Loop body, cont, Dtrue :: s, m)
         (body ++ (Loop body :: cont), s, m)
| stepLoopEnd : forall cont body s m,
    step (Loop body, cont, Dfalse :: s, m)
         (cont, s, m)
.

End Ind_semantics.


(* Second version: with a step function *)
Section Fun_semantics.

Fixpoint step_fun (i : instr) (ix : instructions) (s : stack) (m : memory) : option (instructions * stack * memory) :=
  match i with
    | Drop => if s is x::xs then Some(ix,xs,m) else None
    | If bt bf => if s is x::xs then
                    match x with
                      | Dtrue => Some(bt++ix,s,m)
                      | Dfalse => Some(bf++ix,s,m)
                      | _ => None
                    end else None
    | Loop body => if s is x::xs then
                  match x with
                    | Dtrue => Some(body++(Loop body :: ix),s,m)
                    | Dfalse => Some(ix,s,m)
                    | _ => None
                  end else None
  end.

End Fun_semantics.

End Semantics.