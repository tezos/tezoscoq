From Coq
  Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Data.

(* Inductive tez := Tez : nat -> tez. *)
Axiom tez : Type.
Axiom timestamp : Type.

(* for now, many items are commented as we are trying to get the
architecture right and don't want to get clogged with very similar
cases over and over. As we get more confident that we got things
right, we will uncomment new elements *)

Inductive tagged_data:=
| Int8 : int -> tagged_data
(* | Int16 : int -> tagged_data *)
(* | Int32 : int -> tagged_data *)
| Int64 : int -> tagged_data
(* | Uint8 : int -> tagged_data *)
(* | Uint16 : int -> tagged_data *)
(* | Uint32 : int -> tagged_data *)
(* | Uint64 : int -> tagged_data *)
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

with has_data_type : tagged_data -> type -> Type :=
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

Axiom get_le : tagged_data -> int.

Definition tbool_of_bool b :=
  match b with
    | true => Dtrue
    | false => Dfalse
  end.

Definition get_eq x : tagged_data :=
  match x with
    | Int8 z => tbool_of_bool (z == 0)
    | Int64 z => tbool_of_bool (z == 0)
    | _ => Dfalse
  end.

Definition get_neq x : tagged_data :=
  match x with
    | Int8 z => tbool_of_bool (~~ (z == 0))
    | Int64 z => tbool_of_bool (~~ (z == 0))
    | _ => Dfalse
  end.

Axiom get_lt : tagged_data -> int.

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
  | Nop ;; i2 => Some(i2,s,m)
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


Lemma step_fun_seq : forall i1 i2 s m,
  step_fun (i1 ;; i2) s m = if i1 is NOP then Some(i2,s,m) else if step_fun i1 s m is Some(i,s',m') then
                   Some(i;;i2,s',m')
                 else
                   None.
Proof.
by [].
Qed.

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

Section Path.

Import Option.

Definition ostep_fun state :=
  match state with
    | None => None
    | Some(i,s,m) => step_fun i s m
  end.

Lemma ostep_fun_Nop i2 s m : ostep_fun (ostep_fun (Some(NOP;;i2,s,m))) = ostep_fun (Some(i2,s,m)).
Proof.
by [].
Qed.

Definition evaluate fuel state := iter fuel ostep_fun state.

Lemma evaluate_1 st : evaluate 1 st = ostep_fun st.
Proof.
by [].
Qed.

Lemma evaluate_S f st : evaluate f.+1 st = ostep_fun (evaluate f st).
Proof. by rewrite /evaluate; rewrite iterS. Qed.

Lemma evaluate_Sr f st : evaluate f.+1 st = (evaluate f (ostep_fun st)).
Proof. by rewrite /evaluate; rewrite iterSr. Qed.

Lemma evaluate_None f : evaluate f None = None.
Proof. by elim: f => [|f'] => //= -> . Qed.

Definition evaluate_trace state := traject ostep_fun state.

Definition evaluates state1 state2 := exists f, evaluate f state1 = state2.

Lemma eval_comp : forall f1 f2 st1 st2 st3,
  evaluate f1 st1 = st2 ->
  evaluate f2 st2 = st3 ->
  evaluate (f1 + f2) st1 = st3.
Proof.
elim => [|f1 Hind] f2 st1 st2 st3 .
  by rewrite /=; move ->; rewrite add0n.
rewrite /evaluate.
move => Hev1 Hev2.
by rewrite addnC iter_add Hev1.
Qed.

Definition proj (st : option (instr*stack*memory)) : option (stack * memory) :=
  match st with
    | Some(i,s,m) => Some(s,m)
    | None => None end.

Lemma ostep_fun_seq i1 i2 s m :
  ostep_fun (Some(i1;;i2,s,m)) =
  if i1 is Nop then Some(i2,s,m) else
  if ostep_fun (Some(i1,s,m)) is
  Some(i,s',m') then Some(i;;i2,s',m')
  else None.
Proof.
by case: i1 => // .
Qed.

Lemma evaluates_step_fun i1 s m:
evaluates (Some(i1,s,m)) (ostep_fun (Some(i1,s,m))).
Proof.
by exists 1%N; rewrite evaluate_1.
Qed.

Lemma evaluates_self st : evaluates st st.
Proof.
 by exists 0%N.
Qed.

Lemma evaluates_trans st2 st1 st3 :
  evaluates st1 st2 ->
  evaluates st2 st3 ->
  evaluates st1 st3.
Proof.
move => [f1 Hf1].
move => [f2 Hf2].
exists (f1 + f2)%nat.
move: Hf1 Hf2.
rewrite /evaluate addnC iter_add.
by move => -> ->.
Qed.

(* "minimal" evaluation when an instruction evaluates to NOP at some point. *)
Lemma evaluate_to_NOP i s m s' m' :
  i <> NOP ->
  evaluates (Some (i, s, m)) (Some (NOP, s', m')) ->
  exists f i0 s0 m0,
    evaluate f (Some (i, s, m)) = Some (i0, s0, m0) /\
    i0 <> NOP /\ ostep_fun (Some (i0, s0, m0)) = (Some (NOP, s', m')).
Proof.
  move => Hi [f Hev].
  suff H : (forall (n : nat), (n < f)%N ->
    (forall i0 s0 m0,
      evaluate (f - n.+1) (Some (i, s, m)) = Some (i0, s0, m0) -> i0 <> NOP) ->
    exists (f0 : nat) (i0 : instr) (s0 : stack) (m0 : memory),
  evaluate f0 (Some (i, s, m)) = Some (i0, s0, m0) /\
  i0 <> NOP /\ ostep_fun (Some (i0, s0, m0)) = Some (NOP, s', m')).
  { case: f Hev H => [|f] Hev H.
      by inversion Hev; subst; elim Hi.
    apply: (H f) => // .
    by move => i0 s0 m0; rewrite subnn; case => <-. }
  induction n; intros.
  { destruct f.
    inversion Hev; subst; by elim Hi.
    exists f.
    remember (evaluate f (Some (i, s, m))).
    destruct o as [[[i0 s0] m0]|].
    exists i0, s0, m0. repeat split.
    refine (H0 i0 s0 m0 _).
    rewrite subn1. by symmetry.
    simpl in Hev. by rewrite -Heqo in Hev.
    simpl in Hev. rewrite -Heqo in Hev. inversion Hev. }
  remember (evaluate (f - n.+1) (Some (i, s, m))).
  destruct o as [[[i0 s0] m0]|]; swap 1 2.
  { assert (f = f - n.+1 + n.+1)%N. rewrite subnK; auto.
    rewrite H1 in Hev.
    erewrite eval_comp in Hev; [|reflexivity|reflexivity].
    rewrite -Heqo evaluate_None in Hev. inversion Hev. }
  have: forall i, (i = NOP) \/ (i <> NOP) => [|Hdec].
  { move => i'; case i'; (try by left); intros; right; intro Contra; inversion Contra. }
  case: (Hdec i0) => [Heq|Hi0].
  { exists (f - n.+1 - 1)%N.
  remember (evaluate (f - n.+1 - 1) (Some (i, s, m))).
  destruct o as [[[i1 s1] m1]|]; swap 1 2.
  { assert (f = (f - n.+1 - 1 + (n.+1 + 1)))%N. rewrite -subnDA subnK; auto. by rewrite addn1.
    rewrite H1 in Hev.
    erewrite eval_comp in Hev; [|reflexivity|reflexivity].
    rewrite -Heqo0 evaluate_None in Hev. inversion Hev. }
  exists i1, s1, m1. repeat split.
  refine (H0 i1 s1 m1 _). rewrite Heqo0. f_equal. by rewrite -subnDA addn1.
  subst.
  assert (f = f - n.+1 + n.+1)%N. rewrite subnK; auto.
  rewrite H1 in Hev.
  erewrite eval_comp in Hev; [|reflexivity|reflexivity].
  rewrite -Heqo in Hev.
  rewrite Heqo0. rewrite -evaluate_S.
  assert ((f - n.+1 - 1).+1 = (f - n.+1))%N. rewrite subnSK. by rewrite subn0.
  replace O with (n.+1 - n.+1)%N.
  by apply ltn_sub2r.
  by rewrite subnn.
  rewrite H2 - Heqo.
  revert Hev. clear.
  induction n; intros.
  inversion Hev; by subst.
  rewrite evaluate_Sr in Hev. unfold ostep_fun, step_fun in Hev.
  auto. }
  (* Recursive case. *)
  apply IHn.
  auto.
  intros. inversion H1; by subst.
Qed.

Lemma evaluate_trace_rect_aux
  (i' : instr) (s' : stack) (m' : memory)
  (P : instr -> stack -> memory -> Prop)
  (H0 : P i' s' m')
  (HS : forall i s m i0 s0 m0,
    i <> NOP ->
    evaluates (Some (i, s, m)) (Some (i', s', m')) ->
    ostep_fun (Some (i, s, m)) = Some (i0, s0, m0) ->
    P i0 s0 m0 -> P i s m) :
  forall i s m, i <> NOP -> i' <> NOP -> evaluates (Some (i, s, m)) (Some (i', s', m')) ->
  P i s m.
Proof.
  move => i s m Hi Hneq [f Hev].
  revert i s m Hi Hev.
  induction f; intros.
  { by inversion_clear Hev. }
  rewrite evaluate_Sr in Hev.
  remember (ostep_fun (Some (i, s, m))) as st.
  destruct st as [[[i0 s0] m0]|]; swap 1 2.
  { rewrite evaluate_None in Hev. inversion Hev. }
  have: i0 <> NOP => [|Hi0].
  { intro. subst. apply Hneq.
    revert Hev; clear.
    induction f; intros. by inversion Hev.
    apply IHf. by rewrite evaluate_Sr in Hev. }
  specialize (IHf i0 s0 m0 Hi0 Hev).
  refine (HS _ _ _ _ _ _ Hi _ _ IHf).
  apply: evaluates_trans.
  exists 1%N. symmetry. exact Heqst.
  by exists f%N.
  by symmetry.
Qed.

Theorem evaluate_trace_rect
  (i' : instr) (s' : stack) (m' : memory)
  (P : instr -> stack -> memory -> Prop)
  (H0 : P i' s' m')
  (HS : forall i s m i0 s0 m0,
    i <> NOP ->
    evaluates (Some (i, s, m)) (Some (i', s', m')) ->
    ostep_fun (Some (i, s, m)) = Some (i0, s0, m0) ->
    P i0 s0 m0 -> P i s m) :
  forall i s m, evaluates (Some (i, s, m)) (Some (i', s', m')) ->
  P i s m.
Proof.
  intros.
  have: forall i, (i = NOP) \/ (i <> NOP) => [|Hdec].
  { move => i0; case i0; (try by left); intros; right; intro Contra; inversion Contra. }
  case: (Hdec i) => [Heq|Hi].
  { subst. elim H => [f Hev].
    induction f.
      simpl in Hev. inversion Hev; by subst.
      rewrite evaluate_Sr in Hev.
      by apply IHf. }
  case: (Hdec i') => [Heq|Hi'].
  { subst. destruct (evaluate_to_NOP Hi H) as [f [i0 [s0 [m0 [Hev [Hi0 Hev0]]]]]].
    refine (evaluate_trace_rect_aux P _ _ Hi Hi0 _).
    apply (HS i0 s0 m0 NOP s' m'); trivial. by exists 1%N.
    intros.
    refine (HS _ _ _ _ _ _ H1 _ _ H4).
    apply: evaluates_trans. exact H2. by exists 1%N.
    trivial.
    by exists f. }
  apply: evaluate_trace_rect_aux. exact H0.
  all: done.
Qed.

Lemma ostep_fun_weaken_twosteps i1 i2 s s1 m m1 :
  i1 <> Nop ->
  ostep_fun (Some(i1,s,m)) = (Some(Nop,s1,m1)) ->
  ostep_fun (ostep_fun (Some(i1;;i2,s,m))) = (Some(i2,s1,m1)).
Proof.
move => Hi1 /=.
case: (step_fun i1 s m) => [[[i' s' ] m'] |] // [] -> -> -> /=.
by case Hi1 : i1 => // .
Qed.

Lemma ostep_fun_weaken i1 i1' i2 s s1 m m1 :
  i1 <> Nop ->
  ostep_fun (Some(i1,s,m)) = (Some(i1',s1,m1)) ->
  (ostep_fun (Some(i1;;i2,s,m))) = (Some(i1';;i2,s1,m1)).
Proof.
move => Hi1 /=.
case: (step_fun i1 s m) => [[[i' s' ] m'] |] // [] -> -> -> /=.
by case Hi1 : i1 => // .
Qed.

Lemma evaluates_onestep st1 st2 :
  evaluates (ostep_fun st1) st2 ->
  evaluates st1 st2.
Proof.
by move => [f Hf]; exists f.+1 ;rewrite evaluate_Sr.
Qed.

Lemma evaluates_weaken i1 i1' i2 s s1 m m1 :
  evaluates (Some(i1,s,m)) (Some(i1',s1,m1)) ->
  evaluates (Some(i1;;i2,s,m)) (Some(i1';;i2,s1,m1)).
Proof.
move => Hev1.
refine (evaluate_trace_rect (fun i s m =>
  evaluates (Some (i;; i2, s, m)) _) _ _ Hev1).
  exact: evaluates_self.
move => i s0 m0 i0 s2 m2 HiNOP Hevi Histep Hevseq.
apply: evaluates_onestep.
by rewrite (ostep_fun_weaken _ _ _ _ Histep).
Qed.

Lemma evaluates_seq i1 i2 i3 s m s1 s2 m1 m2:
  evaluates (Some(i1,s,m)) (Some(Nop,s1,m1)) ->
  evaluates (Some(i2,s1,m1)) (Some(i3,s2,m2)) ->
  evaluates (Some(i1;;i2,s,m)) (Some(i3,s2,m2)).
Proof.
move => Hev1 Hev2.
apply: evaluates_trans; last exact: Hev2.
apply: evaluates_trans.
  by apply: evaluates_weaken => //; exact: Hev1.
exact: evaluates_step_fun.
Qed.

Lemma evaluatesEq st1 st2 : evaluates st1 st2 <-> exists f, evaluate f st1 = st2.
Proof.
split => Heval ; last exact: Heval.
  by case: Heval => n; exists n.
Qed.


Lemma evaluates_loop body s m st x :
  has_data_type x t_bool ->
  evaluates (Some(Nop,s,m)) st ->
  evaluates (Some(body ;; (Loop body),s,m)) st ->
  evaluates (Some(Loop body,x::s,m)) st.
Proof.
  move => Htype Hbase Hind.
  inversion Htype; last first.
  - case: Hbase => f Hbase.
    by exists f.+1; rewrite /evaluate iterSr.
  - case: Hind => f Hind.
    by exists f.+1; rewrite /evaluate iterSr.
Qed.


Lemma evaluates_if bt bf x s m st :
  has_data_type x t_bool ->
  (x = Dtrue -> evaluates (Some(bt,s,m)) st) ->
  (x = Dfalse -> evaluates (Some(bf,s,m)) st) ->
  evaluates (Some(If bt bf,x::s,m)) st.
Proof.
move => Htype.
inversion Htype.
- case: x H Htype => // _ _ Htrue.
  case: Htrue => // f1 Hev1 _.
  by exists f1.+1; move: Hev1; rewrite /evaluate iterSr /=.
- case: x H Htype => // _ _ _ Hfalse.
  case: Hfalse => // f2 Hev2.
  by exists f2.+1; move: Hev2; rewrite /evaluate iterSr /=.
Qed.

Lemma factorial_correct_eval m1 (n : nat) : evaluates (Some(factorial_program, [::Int64 (n%:Z)],m1)) (Some(Nop,[::Int64 ((factorial n)%:Z)],m1)).
Proof.
do 4 apply: evaluates_onestep => /= .
apply: evaluates_if; case Hn : n => [|n1] // .
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
      b = get_neq (Int64 z) ->
      b1 = get_neq (Int64 (z-1)) ->
      evaluates ((Some(LOOP {{ body }},[:: b; Int64 z; Int64 zacc],m1))) (Some(LOOP {{body}},[:: b1 ; Int64 (z-1)%Z; Int64 (z*zacc)],m1)).
    move =>  H1 H2 H3.
    apply: evaluates_onestep => /= .
    have -> : b = Dtrue.
      rewrite H2 /=; suff -> : z != 0; first by [].
      apply/negP; rewrite eq_sym => Hz0.
      by move/eqP in Hz0; rewrite -Hz0 in H1.
    do 14 apply: evaluates_onestep => /= .
    exists 0%N => /= .
    congr (Some _);congr(_,_,_);congr([::_;_;_]).
    by rewrite H3.
  apply: (@evaluates_seq _ _ _ _ _ ([::Int64 0; Int64 ((n1.+1)`!)%:Z])); last first => // .
    by apply: evaluates_onestep => /= ; exists 0%N.
  (* Generalize the goal a little bit. *)
  suff {Hn n1} H  : (forall N acc, acc * (Posz (factorial n)) = factorial N ->
    evaluates (Some (LOOP {{body}}, [:: get_neq (Int64 n); Int64 n; Int64 acc], m1))
      (Some (NOP, [:: Int64 0; Int64 N`!], m1))).
    specialize (H n 1).
    replace Dtrue with (get_neq (Int64 n)) by by subst.
    rewrite -Hn; apply: H; apply: mul1r.
  elim: n => [|n0 HIn] N acc H.
    by apply: evaluates_onestep => /= ; rewrite -H fact0 mulr1; exact: evaluates_self.
  apply: (@evaluates_trans _ (Some(_,[::_;_;_],_))); first exact: Hsuff.
  specialize (HIn N (Posz n0.+1 * acc)).
  have -> : (Posz n0.+1 - 1) = (Posz n0) by rewrite intS -addrAC subrr add0r.
  by apply: HIn; rewrite -H factS PoszM mulrCA mulrA.
Qed.

End Path.


(* Fixpoint evaluate (i : instr) (s : stack) (m : memory) (f : nat) : option (instr*stack * memory) := *)
(*   match f with *)
(*   | 0 => Some(i,s,m) *)
(*   | S f => match step_fun i s m with *)
(*             | None => None *)
(*             | Some(pgm',s',m') => evaluate pgm' s' m' f *)
(*           end *)
(*   end. *)

(* (* Lemma eval_nop pgm m1 f s : evaluate (NOP ;; pgm) s m1 f = evaluate pgm s m1 f. *) *)
(* (* Proof. *) *)
(* (*   case: f => //=. *) *)
(* (* Qed. *) *)

(* Lemma eval_seq s m1 f i : evaluate i s m1 f = *)
(*   match f with *)
(*   | 0 => Some(i,s,m1) *)
(*   | S f => match step_fun i s m1 with *)
(*             | None => None *)
(*             | Some(pgm',s',m') => evaluate pgm' s' m' f *)
(*           end *)
(*   end. *)
(* Proof. *)
(*  by case: f => // f. *)
(* Qed. *)

(* Lemma eval_assoc i1 i2 i3 s m1 f : evaluate ((i1 ;; i2) ;; i3) s m1 f = evaluate (i1;;i2;;i3) s m1 f. *)
(* Proof. *)
(* Admitted. *)

(* Lemma eval_comp : forall f1 f2 i1 i2 s1 s2 m1 m2 final_state, *)
(*   evaluate i1 s1 m1 f1 = Some(i2,s2,m2) -> *)
(*   evaluate i2 s2 m2 f2 = final_state -> *)
(*   evaluate i1 s1 m1 (f1 + f2) = final_state. *)
(* Proof. *)
(* elim => [|f1 Hind] f2 i1 i2 s1 s2 m1 m2 final_state. *)
(*   by rewrite add0n /= => [[]] -> -> ->. *)
(* move => Hev1 Hev2. *)
(* rewrite /= in Hev1; move: Hev1. *)
(* case: (step_fun i1 s1 m1). => // [[[a s] m]] Hev1. *)
(* rewrite addSnnS. apply :Hind. *)

(* Inductive evaluates : instr -> stack -> memory -> option (instr * stack * memory) -> Type := *)
(* | evaluates_self : forall i s m, evaluates i s m (Some(i,s,m)) *)
(* | evaluates_trans :  *)
(*     forall i s m i' s' m' i'' s'' m'',  *)
(*       evaluates i s m (Some (i',s',m')) ->  *)
(*       evaluates i' s' m' (Some (i'',s'',m'')) ->  *)
(*       evaluates (i;;i') s m (Some (i'',s'',m'')) *)
(* | evaluates_stepfun : forall i s m, evaluates i s m (step_fun i s m). *)

(* Lemma foo : forall i s m final_state,  *)
(*               evaluates i s m final_state ->  *)
(*               exists f, evaluate i s m f =  *)
(*                         match final_state with  *)
(*                           | None => None *)
(*                           | Some(i,s,m) => Some(i,s,m) end. *)
(* Proof. *)
(* move => i s m fs. *)
(* elim. *)
(* - move => i0 s0 m0. *)
(*   by exists 0. *)
(* - move => i0 s0 m0 i' s' m' i'' s'' m'' Hev1 [f1 Hf1] Hev2 [f2 Hf2]. *)
(*   exists (f1 + f2). *)

(* elim. *)
(* move => i Hind i' Hindi' s m fs Hev. *)
(* elim: Hev. *)
(* move => i0 s0 m0. *)
(* - by exists 0. *)
(* - move => i0 s0 m0 i'0 s' m' i'' s'' m''. *)
(*   move => Hev1 [f1 Hf1] Hev2 [f2 Hf2]. *)
(*   exists (f1 + f2). rewrite eval_seq. rewrite step_fun_seq. *)

(* Fixpoint evaluate_trace (i : instr) (s : stack) (m : memory) (trace : list stack) (f : nat) : option (list stack * memory) := *)
(*   match f with *)
(*   | 0 => Some(trace,m) *)
(*   | S f => if i is Nop then Some(trace,m) else match step_fun i s m with *)
(*             | None => None *)
(*             | Some(pgm',s',m') => evaluate_trace pgm' s' m' (s'::trace) f *)
(*           end *)
(*   end. *)


Variable m : memory.

Eval native_compute in evaluate 1000 (Some(factorial_program,[::Int64 6],m)).
Eval native_compute in evaluate_trace (Some(factorial_program,[::Int64 5],m)) 100 .
Eval native_compute in step_fun (DROP ;; DROP) [::Int8 1;Int8 1] m.
Eval compute in step_fun (NOP ;; DROP) [::Int8 1] m.
Eval compute in evaluate 1 (Some(DROP,[::Int8 1; Int8 1],m)).
Eval compute in evaluate 100 (Some((DROP ;; DROP),[::Int8 1;Int8 1],m)).





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
