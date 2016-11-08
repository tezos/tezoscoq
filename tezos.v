From Coq
  Require Import ZArith String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool ssrnat seq.

Set Implicit Arguments.

Section Data.

(* Inductive tez := Tez : nat -> tez. *)
Axiom tez : Type.
Axiom timestamp : Type.

(* for now, many items are commented as we are trying to get the
architecture right and don't want to get clogged with very similar
cases over and over. As we get more confident that we got things
right, we will uncomment new elements *)

Inductive tagged_data:=
| Int8 : Z -> tagged_data
(* | Int16 : Z -> tagged_data *)
(* | Int32 : Z -> tagged_data *)
| Int64 : Z -> tagged_data
(* | Uint8 : Z -> tagged_data *)
(* | Uint16 : Z -> tagged_data *)
(* | Uint32 : Z -> tagged_data *)
(* | Uint64 : Z -> tagged_data *)
| Void
| Dtrue
| Dfalse
| DString : string -> tagged_data
(* | <float constant> *)
| Timestamp : timestamp -> tagged_data
(* | Signature <signature constant> *)
| DTez : tez -> tagged_data
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
| DPair : tagged_data -> tagged_data -> tagged_data.
(* | Pair <type> <type> <untagged data> <untagged data> *)
(* | List <type> <untagged data> ... *)
(* | Set <comparable type> <untagged data> ... *)
(* | Map <comparable type> <type> (Item <untagged data> <untagged data>) ... *)
(* | Contract <type> <type> <contract constant> *)
(* | Lambda <type> <type> { <instruction> ... } *)

Definition is_comparable (d : tagged_data) : bool :=
  match d with
    | Int8 z  => true
    | Int64 i => true
    | Dtrue | Dfalse => true
    | DTez t => true
    | _ => false
  end.

Definition is_bool d :=
  match d with
    | Dtrue => true
    | Dfalse => true
    | _ => false
  end.

Definition is_int i :=
  match i with
    | Int8 _ => true
    | Int64 _ => true
    | _ => false
  end.

Definition stack := list tagged_data.

End Data.

Section Instructions.

Inductive instr :=
| Seq : instr -> instr -> instr
| Nop : instr
| If : instr -> instr -> instr
| Loop : instr -> instr
| Dip : instr -> instr
| Drop : instr
| Dup : instr
| Swap : instr
| Push : tagged_data -> instr
| Pair : instr
| Eq : instr
| Neq : instr
| Lt : instr
| Not : instr
| And : instr
| Or : instr
| Mul : instr
| Sub : instr
.

End Instructions.

(* Notations don't survive the end of section:
   that's why they are here *)
Notation "c1 ';;' c2" := (Seq c1 c2) (at level 80, right associativity).
Notation "'NOP'" := (Nop).
Notation "'IFB' '{{' bt '}}' '{{' bf '}}'" := (If bt bf) (at level 80, right associativity).
Notation "'LOOP' '{{' body '}}'" := (Loop body) (at level 80, right associativity).
Notation "'DIP' '{{' code '}}'" := (Dip code) (at level 80, right associativity).
Notation "'DROP'" := (Drop).
Notation "'DUP'" := (Dup).
Notation "'SWAP'" := (Swap).
Notation "'PUSH' x" := (Push x) (at level 35).
Notation "'EQ'" := (Eq).
Notation "'NEQ'" := (Neq).
Notation "'LT'" := (Lt).
Notation "'NOT'" := (Not).
Notation "'AND'" := (And).
Notation "'OR'" := (Or).
Notation "'MUL'" := (Mul).
Notation "'SUB'" := (Sub).

(* tests for notation precedence levels and associativity *)
Section NotationTests.

(* TODO: we might need to move this somewhere else and add some tests when we introduce notation for typing, etc. *)

Goal
  (DROP ;; DROP ;; NOP) =
  Seq Drop (Seq Drop Nop). done. Qed.
Goal
  (PUSH Dtrue ;; IFB {{ NOP ;; NOP }} {{ NOP }}) =
  (Seq (Push Dtrue) (If (Seq Nop Nop) Nop)). done. Qed.

End NotationTests.


Section Types.

(** The type of an instruction consists of 2 components:
    a list of types it consumes (from the stack) and
    a list of types it produces (pushes on the stack). *)
Inductive instr_type :=
| Arrow : list type -> list type -> instr_type

with type :=
| t_int8 : type
| t_int64 : type
(*| t_void : type*)
| t_bool : type
(*| t_string : type*)
(*| t_tez : tez -> type*)
(*| t_contract : type -> type -> type*)
(*| t_quotation : instr_type -> type*)
.

Definition stack_type := list type.

End Types.

Infix "-->" := Arrow (at level 75).

(* Section TypingJudgements. *)   (* TODO: Notations won't survive the end of the section. Can we do anything about this? *)

(** Composition relation between instruction types.
    It's meant to be used for typing the `Seq` instruction. *)
Reserved Notation "IT1 '<o>' IT2 '===' IT3" (at level 70).
Inductive instr_type_composition : instr_type -> instr_type -> instr_type -> Prop :=
| IT_comp_nil1 : forall Sa Sc Sd,
    (** When 1st instruction doesn't produce output,
        the input stack must have all the elements
        for 1st _and_ 2nd instructions beforehand *)
    (Sa --> []) <o> (Sc --> Sd) === (Sa ++ Sc --> Sd)
| IT_comp_nil2 : forall Sa Sb Sd,
    (** When 2nd instruction doesn't consume input,
        it's output gets added to the output of 1st instruction *)
    (Sa --> Sb) <o> ([] --> Sd) === (Sa --> Sd ++ Sb)
| IT_comp_cons : forall Sa Sb Sc Sd Sx Sy t,
    (Sa --> Sb) <o> (Sc --> Sd) === (Sx --> Sy) ->
    (** When 1st instruction produces a value of type `t`,
        2nd instruction must consume a value of the same type *)
    (Sa --> t :: Sb) <o> (t :: Sc --> Sd) === (Sx --> Sy)
where "IT1 '<o>' IT2 '===' IT3" := (instr_type_composition IT1 IT2 IT3).

Hint Constructors instr_type_composition.

Reserved Notation "i ':i:' IT" (at level 40).
Reserved Notation "d ':d:' DT" (at level 40).
Inductive has_instr_type : instr -> instr_type -> Prop :=
| IT_Seq : forall i1 i2 Sa Sb Sc Sd Sx Sy,
    i1 :i: (Sa --> Sb) ->
    i2 :i: (Sc --> Sd) ->
    (Sa --> Sb) <o> (Sc --> Sd) === (Sx --> Sy) ->
    (i1 ;; i2) :i: (Sx --> Sy)
| IT_Nop :
    NOP :i: ([] --> [])
| IT_Drop : forall t,
    DROP :i: ([ t ] --> [])
| IT_Dup : forall t,
    DUP :i: ([ t ] --> [ t ; t ])
| IT_Swap : forall t1 t2,
    SWAP :i: ([ t1 ; t2 ] --> [ t2 ; t1 ])
| IT_Push : forall v t,
    has_data_type v t ->
    PUSH v :i: ([] --> [ t ])
| IT_Dip : forall t code Sa Sb,
    code :i: (Sa --> Sb) ->
    (DIP {{ code }}) :i: (t :: Sa --> t :: Sb)
| IT_If : forall Sa Sb bt bf,
    bt :i: (Sa --> Sb) ->
    bf :i: (Sa --> Sb) ->
    (IFB {{ bt }} {{ bf }}) :i: (t_bool :: Sa --> Sb)
| IT_Loop : forall S body,
    body :i: (S --> t_bool :: S) ->
    (LOOP {{ body }}) :i: (t_bool :: S --> S)
| IT_Eq :
    EQ :i: ([ t_int64 ] --> [ t_bool ])
| IT_Neq :
    NEQ :i: ([ t_int64 ] --> [ t_bool ])
(* TODO: redefine IT_Mul to take into account other integer (arithmetic?) data types *)
| IT_Mul :
    MUL :i: ([ t_int64 ; t_int64 ] --> [ t_int64 ])
(* TODO: redefine IT_Sub to take into account other integer (arithmetic?) data types *)
| IT_Sub :
    SUB :i: ([ t_int64 ; t_int64 ] --> [ t_int64 ])
where "i ':i:' IT" := (has_instr_type i IT)

with has_data_type : tagged_data -> type -> Prop :=
| T_boolT : Dtrue :d: t_bool
| T_boolF : Dfalse :d: t_bool
| T_Int64 : forall z, Int64 z :d: t_int64
| T_Int8 : forall z, Int8 z :d: t_int8
where "d ':d:' DT" := (has_data_type d DT).

Hint Constructors has_instr_type.
Hint Constructors has_data_type.
Hint Resolve cats0.
(* instr_type_composition is going to produce a lot of subterms
   of the form `xs ++ [::]`, that's why the following hint might
   come in handy *)
Hint Extern 4 ((_ = _)) => repeat rewrite cats0.

(* a test for the `repeat rewrite cats0` hint *)
Goal forall (T : Type) (xs : seq T), ((xs ++ []) ++ []) ++ [] = xs.
  auto. Qed.

(* The `instr_type_composition` relation is
   a partial binary function *)
Lemma instr_type_composition_functional : forall STa STb ST1 ST2,
  STa <o> STb === ST1 ->
  STa <o> STb === ST2 ->
  ST1 = ST2.
Proof.
move => STa STb ST1 ST2 H1 H2.
elim: H1 H2.
- move => Sa Sc Sd Hc2. by inversion Hc2; auto.
- move => Sa Sb Sd Hc2. by inversion Hc2; auto.
- move => Sa Sb Sc Sd Sx Sy t Hc1 IH Hc2.
  by inversion Hc2; subst; intuition.
Qed.

(*End TypingJudgements.*)

Section Typechecking_Tests.

(*
   The following tactic should've been implemented just with
   `econstructor` all the way down.
   For some reason Coq can't unify arguments when it comes to
   applying IT_comp_nil1 or IT_comp_nil2 using `apply` or `econstructor`.
   `refine (<constructor_name> _ _ _)` works, but this is obviously a crutch.

TODO: find a way to implement this more elegantly.

For example, then typechecking

  (DROP ;; DROP) :i: ([t1 ; t2] --> []).

When it comes to the last `econstructor` application we have the following two terms to unify:
?X   --> [] // ?Y   --> ?Z \\ ?X ++ ?Y  --> ?Z
with
[?A] --> [] // [?B] --> [] \\ [t1; t2] --> []

This is obviously can be done:
?X = [?A]  |  ?Y = [?B]  |   ?Z = []
And
[?A] ++ [?B] = [t1; t2]
?A = t1
?B = t2
 *)

Ltac typecheck_program :=
  tryif econstructor
    then typecheck_program
    else refine (IT_comp_nil1 _ _ _) || refine (IT_comp_nil2 _ _ _).

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
  (PUSH (Int64 0) ;; DROP) :i: ([] --> []).
Proof. by typecheck_program. Qed.

Example typing_push_drop2 :
  (DUP ;;
   EQ ;;
   IFB {{ DROP ;; PUSH (Int64 0) }}
       {{ DROP ;; PUSH (Int64 0) }})
  :i: ([t_int64] --> [t_int64]).
Proof. by typecheck_program. Qed.

Definition factorial_program :=
  (* stack state is given in the comments below *)
  (* [ n ] -- input parameter, n >= 0 *)
  DUP ;;
  (* [ n ; n ] *)
  EQ ;;
  (* [ (n = 0)? ; n ] *)
  IFB {{ DROP ;;
        (* [] *)
        PUSH (Int64 1)
        (* [ 1 ] *) }}        (* return 0! = 1 *)
      {{ PUSH (Int64 1) ;;    (* push accumulator's initial value *)
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
          PUSH (Int64 1) ;;
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
  factorial_program :i: ([t_int64] --> [t_int64]).
Proof. by typecheck_program. Qed.

(* TODO: add some more tests for typechecking *)

(* XXX: variadic functions are not allowed! (i.e. a program which empties its input stack must not typecheck!)
*)

End Typechecking_Tests.

Section Semantics.

Axiom memory : Type.

(* Second version: with a step function *)
Section Fun_semantics.

(* I'm guessing these will be replaced by accesses to memory, with a
precise spec *)
Axiom get_timestamp : unit -> timestamp.
Axiom get_current_amount : unit -> tez.

(* these axioms to model the behavior of Transfer_funds, which I do
not understand as of now *)
Axiom get_new_global : tagged_data -> tagged_data.
Axiom get_return_value : tagged_data -> tagged_data.

Axiom get_le : tagged_data -> Z.

Definition tbool_of_bool b :=
  match b with
    | true => Dtrue
    | false => Dfalse
  end.

Definition get_eq x : tagged_data :=
  match x with
    | Int8 z => tbool_of_bool (Zeq_bool z 0)
    | Int64 z => tbool_of_bool (Zeq_bool z 0)
    | _ => Dfalse
  end.

Definition get_neq x : tagged_data :=
  match x with
    | Int8 z => tbool_of_bool (negb (Zeq_bool z 0))
    | Int64 z => tbool_of_bool (negb (Zeq_bool z 0))
    | _ => Dfalse
  end.
Axiom get_lt : tagged_data -> Z.



Definition get_mul (x : tagged_data) (y : tagged_data) : option tagged_data :=
  match x,y with
    | Int8 x,Int8 y => Some(Int8 (x * y))
    | Int64 x,Int64 y => Some(Int64 (x * y))
    | _,_ => None
  end.

Definition get_sub (x : tagged_data) (y : tagged_data) : option tagged_data :=
  match x,y with
    | Int8 x,Int8 y => Some(Int8 (x - y))
    | Int64 x,Int64 y => Some(Int64 (x - y))
    | _,_ => None
  end.

Fixpoint step_fun (i : instr) (s : stack) (m : memory) : option (instr * stack * memory) :=
  match i with
  | Nop ;; i2 => step_fun i2 s m
  | i1 ;; i2 => if step_fun i1 s m is Some(i,s',m') then
                   Some(i;;i2,s',m')
                 else
                   None
  | Nop => Some(Nop,s,m)
  | If bt bf => if s is x::s then
                 match x with
                   | Dtrue => Some(bt,s,m)
                   | Dfalse => Some(bf,s,m)
                   | _ => None
                 end else None
  | Loop body => if s is x::s then
                  match x with
                  | Dtrue => Some(body ;;(Loop body),s,m)
                  | Dfalse => Some(Nop,s,m) (* doubtful *)
                  | _ => None
                  end else None
  | Dip i1 => if s is x::s then
                     match step_fun i1 s m with
                       | Some (i2,s',m') => Some(i2,x::s',m')
                       | None => None
                     end else None
  | Drop => if s is x::xs then Some(Nop,xs,m) else None
  | Dup => if s is x::xs then Some(Nop,x::x::xs,m) else None
  | Swap => if s is x1::x2::s then Some(Nop,x2::x1::s,m) else None
  | Push d => Some(Nop,d::s,m)
  | Pair => if s is a::b::s then Some(Nop,(DPair a b)::s,m) else None
  | Eq => if s is x::s then if is_comparable x then Some(Nop,((get_eq x))::s,m) else None else None
  | Neq => if s is x::s then if is_comparable x then Some(Nop,((get_neq x))::s,m) else None else None
  | Lt => if s is x::s then if is_comparable x then Some(Nop,(Int64 (get_lt x))::s,m) else None else None
  | Not => if s is x::s then match x with
                              | Dtrue => Some(Nop,Dfalse::s,m)
                              | Dfalse => Some(Nop,Dtrue::s,m)
                              | _ => None
                            end else None
  | And => if s is x1::x2::s then
            if (is_bool x1 && is_bool x2) then
              match (x1,x2) with
                | (Dtrue,Dtrue) => Some(Nop,Dtrue::s,m)
                | (_,_) => Some(Nop,Dfalse::s,m)
              end else None
          else None
  | Or => if s is x1::x2::s then
            if (is_bool x1 && is_bool x2) then
              match (x1,x2) with
                | (Dtrue,_) => Some(Nop,Dtrue::s,m)
                | (_,Dtrue) => Some(Nop,Dtrue::s,m)
                | (_,_) => Some(Nop,Dfalse::s,m)
              end else None
          else None
  | Mul => if s is x1::x2::s then
            match (get_mul x1 x2) with
              | Some(x12) => Some(Nop,x12::s,m)
              | None => None
          end else None
  | Sub => if s is x1::x2::s then
            match (get_sub x1 x2) with
              | Some(x12) => Some(Nop,x12::s,m)
              | None => None
          end else None

end.

(* Fixpoint step_fun (i : instr) (pgm : instr) (s : stack) (m : memory) : option (instr * stack * memory) := *)
(*   match i with *)
(*   | i1 ;; i2 => step_fun i1 (i2 ;; pgm) s m *)
(*   (* the Nop case is not very satisfying *) *)
(*   | Nop => Nonematch pgm with *)
(*             | Nop => Some(Nop,s,m) *)
(*             | Seq i1 i2 => step_fun i1 i2 s m *)
(*           end *)
(*   | If bt bf => if s is x::s then *)
(*                  match x with *)
(*                    | Dtrue => Some(bt ;; pgm,s,m) *)
(*                    | Dfalse => Some(bf ;; pgm,s,m) *)
(*                    | _ => None *)
(*                  end else None *)
(*   | Loop body => if s is x::s then *)
(*                   match x with *)
(*                   | Dtrue => Some(body ;;((Loop body) ;; pgm),s,m) *)
(*                   | Dfalse => Some(pgm,s,m) *)
(*                   | _ => None *)
(*                   end else None *)
(*   | Dip i1 => if s is x::s then *)
(*                      match step_fun i1 pgm s m with *)
(*                        | Some (i2,s',m') => Some(i2,x::s',m') *)
(*                        | None => None *)
(*                      end else None *)
(*   | Drop => if s is x::xs then Some(pgm,xs,m) else None *)
(*   | Dup => if s is x::xs then Some(pgm,x::x::xs,m) else None *)
(*   | Swap => if s is x1::x2::s then Some(pgm,x2::x2::s,m) else None *)
(*   | Push d => Some(pgm,d::s,m) *)
(*   | Pair => if s is a::b::s then Some(pgm,(DPair a b)::s,m) else None *)
(*   | Eq => if s is x::s then if is_comparable x then Some(pgm,(Int64 (get_eq x))::s,m) else None else None *)
(*   | Neq => if s is x::s then if is_comparable x then Some(pgm,(Int64 (get_neq x))::s,m) else None else None *)
(*   | Lt => if s is x::s then if is_comparable x then Some(pgm,(Int64 (get_lt x))::s,m) else None else None *)
(*   | Not => if s is x::s then match x with *)
(*                               | Dtrue => Some(pgm,Dfalse::s,m) *)
(*                               | Dfalse => Some(pgm,Dtrue::s,m) *)
(*                               | _ => None *)
(*                             end else None *)
(*   | And => if s is x1::x2::s then *)
(*             if (is_bool x1 && is_bool x2) then *)
(*               match (x1,x2) with *)
(*                 | (Dtrue,Dtrue) => Some(pgm,Dtrue::s,m) *)
(*                 | (_,_) => Some(pgm,Dfalse::s,m) *)
(*               end else None *)
(*           else None *)
(*   | Or => if s is x1::x2::s then *)
(*             if (is_bool x1 && is_bool x2) then *)
(*               match (x1,x2) with *)
(*                 | (Dtrue,_) => Some(pgm,Dtrue::s,m) *)
(*                 | (_,Dtrue) => Some(pgm,Dtrue::s,m) *)
(*                 | (_,_) => Some(pgm,Dfalse::s,m) *)
(*               end else None *)
(*           else None *)
(*   | Mul => if s is x1::x2::s then *)
(*             match (get_mul x1 x2) with *)
(*               | Some(x12) => Some(pgm,x12::s,m) *)
(*               | None => None *)
(*           end else None *)
(*   | Sub => if s is x1::x2::s then *)
(*             match (get_sub x1 x2) with *)
(*               | Some(x12) => Some(pgm,x12::s,m) *)
(*               | None => None *)
(*           end else None *)

  (* | Le => if s is x::s then if is_comparable x then Some(pgm,(Int64 (get_le x))::s,m) else None else None *)
  (* | Transfer_funds => if s is p::amount::contract::g::nil then *)
  (*                 Some(pgm,[::get_return_value contract;get_new_global g],m) else None *)
  (* | Now => Some(pgm,Timestamp (get_timestamp tt)::s,m) *)
  (* | Balance => Some(pgm,DTez (get_current_amount tt)::s,m) *)
  (* end. *)






(* | Sub : instr *)
(* . *)


Fixpoint evaluate (i : instr) (s : stack) (m : memory) (f : nat) : option (stack * memory) :=
  match f with
  | 0 => Some(s,m)
  | S f => match step_fun i s m with
            | None => None
            | Some(pgm',s',m') => evaluate pgm' s' m' f
          end
  end.

Fixpoint evaluate_trace (i : instr) (s : stack) (m : memory) (trace : list stack) (f : nat) : option (list stack * memory) :=
  match f with
  | 0 => Some(trace,m)
  | S f => if i is Nop then Some(trace,m) else match step_fun i s m with
            | None => None
            | Some(pgm',s',m') => evaluate_trace pgm' s' m' (s'::trace) f
          end
  end.


Variable m : memory.

Eval compute in evaluate factorial_program [::Int64 5] m 1000.
Eval compute in evaluate_trace factorial_program [::Int64 5] m [::[::Int64 5]] 100.
Eval compute in step_fun (DROP ;; DROP) [::Int8 1;Int8 1] m.
Eval compute in step_fun (NOP ;; DROP) [::Int8 1] m.
Eval compute in evaluate (DROP) [::Int8 1; Int8 1] m 1.
Eval compute in evaluate (DROP ;; DROP) [::Int8 1;Int8 1] m 100.

(* these lemmas need to be reformulated *)

(* Lemma has_prog_type_cat : forall p q st1 st2 st3, *)
(*   has_prog_type p (Pre_post st1 st2) -> *)
(*   has_prog_type q (Pre_post st2 st3) -> *)
(*   has_prog_type (p++q) (Pre_post st1 st3). *)
(* Proof. *)
(* elim => [|p ps Hps] q st1 st2 st3. *)
(* - by move => Hnil; inversion Hnil. *)
(* - by move => Hp Hq; inversion Hp; econstructor; eauto. *)
(* Qed. *)

(* Lemma step_fun_preserves_type i st1 st2 s m f : *)
(*   has_prog_type i (Pre_post st1 st2) -> *)
(*   has_stack_type s st1 -> *)
(*   match (evaluate i s m f) with *)
(*   | Some (s',m') => has_stack_type s' st2 *)
(*   | None => True *)
(*   end. *)
(* Proof. *)
(* move: f pgm st1 st2 s m. *)
(* elim => [|f HIf] pgm st1 st2 s m //. *)
(* case: pgm => [| i pgm] // . *)
(*   by move => HPT; inversion HPT => HST //=. *)
(* case: i => [| | (* Push *) d| | (* If *) bt bf| (* Loop *)body| (* Le *) | | |] /=. *)
(* - case: s => [| x s]// . *)
(*   move => HPT HST. *)
(*   inversion HPT. *)
(*   inversion HST. *)
(*   inversion H2. *)
(*   apply: HIf. *)
(*     exact: H4. *)
(*   rewrite -H8 in H10. *)
(*   case: H10. *)
(*     by move => _; rewrite -H11 => -> . *)
(* - admit. (* TODO : Dup *) *)
(* - admit. (* TODO : Push *) *)
(* - admit. (* TODO : Pair *) *)
(* - case: s => [| x s] //; case: x => // . *)
(*   + move => HPT HST. *)
(*     inversion HPT. *)
(*     inversion H2. *)
(*     apply: HIf. *)
(*       apply: has_prog_type_cat. *)
(*         exact: H12. *)
(*         exact: H4. *)
(*     rewrite -H7 in HST. *)
(*     by inversion HST. *)
(*   + move => HPT HST. *)
(*     inversion HPT. *)
(*     inversion H2. *)
(*     apply: HIf. *)
(*       apply: has_prog_type_cat. *)
(*         exact: H13. *)
(*         exact: H4. *)
(*     rewrite -H7 in HST. *)
(*     by inversion HST. *)
(* - case: s => [| x s] //; case: x => // ; last first. *)
(*   + move => HPT HST. *)
(*     inversion HPT. *)
(*     apply: HIf. *)
(*       exact: H4. *)
(*     inversion HST. *)
(*     inversion H2. *)
(*     rewrite -H8 in H11. *)
(*     case: H11 => _. *)
(*     by rewrite -H12 => -> . *)
(*   + move => HPT HST. *)
(*     inversion HPT. *)
(*     inversion H2. *)
(*     apply: HIf. *)
(*       * apply: has_prog_type_cat. *)
(*           exact: H10. *)
(*         apply: PT_seq. *)
(*           apply: IT_Loop. *)
(*             exact: H9. *)
(*           exact: H10. *)
(*         exact: H4. *)
(*       * inversion HST. *)
(*         rewrite -H6 in H14. *)
(*         case: H14 => _. *)
(*           by rewrite -H7 => <- . *)
(* - admit. (* TODO : Le *) *)
(* - admit. (* TODO : Transfer_funds *) *)
(* - admit. (* TODO : Now *) *)
(* - admit. (* TODO : Balance *) *)
(* Admitted. *)

End Fun_semantics.
