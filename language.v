From Coq Require Import String List.
Import ListNotations.
From mathcomp.ssreflect
  Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp.algebra
  Require Import ssralg ssrnum ssrint.
Set Implicit Arguments.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Types.

Inductive instr_type :=
| Arrow : list type -> list type -> instr_type

with type :=
| t_int
| t_bool : type
| t_pair : type -> type -> type
| t_option : type -> type
| t_list : type -> type
| t_string : type
| t_map : type -> type -> type
| t_signature : type
| t_key : type
| t_tez : type
| t_contract : type -> type -> type
| t_void : type
| t_quotation : instr_type -> type.

Definition stack_type := list type.
End Types.

Infix "-->" := Arrow (at level 75).

Section DataAndInstr.

Inductive tez := Tez : nat -> tez.
Axiom timestamp : Type.

(* Definition Map (A : Type) (B : Type) := list (prod A B). *)
(* Definition empty_map A B : Map A B := @nil (prod A B). *)

(* Definition get A B (m : Map A B) (x : A) := None. *)

(* please kill me now *)
(* Axiom Map : Type. *)
(* Axiom empty_map : Map. *)
(* Axiom get : forall A B (m : Map A B) (x : A), option A. *)
(* Axiom put : forall A B (m : Map A B) (x : A), Map A B. *)

(* for now, many items are commented as we are trying to get the
architecture right and don't want to get clogged with very similar
cases over and over. As we get more confident that we got things
right, we will uncomment new elements *)

Section Map.
(* purely mathematical view of functional maps *)

Definition myMap A B := list (prod A B).

Definition empty_map {A} {B} := @nil (prod A B).

Definition put {A B} (key : A) (value : B) (m : myMap A B) : myMap A B :=
(key,value)::m.

Definition contains {A} {B}
(eq : A -> A -> bool) (k : A) (v : B) (m : myMap A B) :=
  has (fun kv => eq kv.1 k) m.

Definition remove {A} {B}
  (eq : A -> A -> bool) (k : A) (v : B) (m : myMap A B) :=
  (filter (fun kv => eq kv.1 k) m).

Definition checked_put {A} {B} eq (k : A) (v : B) m :=
  (k,v)::(remove eq k v m).

End Map.
Inductive tagged_data:=
| Int : int -> tagged_data
| Void
| DBool : bool -> tagged_data
| DString : string -> tagged_data
| Timestamp : timestamp -> tagged_data
| DTez : tez -> tagged_data
| DPair : tagged_data -> tagged_data -> tagged_data
| DMap : myMap tagged_data tagged_data -> tagged_data
| DLambda : instr -> tagged_data
with
instr : Type :=
| Seq : instr -> instr -> instr
| Done : instr
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
| Ge : instr
| Not : instr
| And : instr
| Or : instr
| Mul : instr
| Add : instr
| Sub : instr
| Lambda : instr -> instr
| If_some : instr -> instr -> instr
| Compare : instr
| Car : instr
| Cdr : instr
| Hash : instr
| Get : instr
| Fail : instr
| Check_signature : instr
| Map_reduce : instr
| Transfer_funds : instr
.


(* | Signature <signature constant> *)
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
(* | Pair <type> <type> <untagged data> <untagged data> *)
(* | List <type> <untagged data> ... *)
(* | Set <comparable type> <untagged data> ... *)
(* | Map <comparable type> <type> (Item <untagged data> <untagged data>) ... *)
(* | Contract <type> <type> <contract constant> *)
(* | Lambda <type> <type> { <instruction> ... } *)

Definition is_comparable (d : tagged_data) : bool :=
  match d with
    | Int _ | DBool _ | DTez _ => true
    | _ => false
  end.

Definition is_bool d :=
  match d with
    | DBool _ => true
    | _ => false
  end.

Definition is_int i :=
  match i with
    | Int _ => true
    | _ => false
  end.

Definition stack := list tagged_data.

End DataAndInstr.

(* Notations don't survive the end of section:
   that's why they are here *)
Notation "c1 ';;' c2" := (Seq c1 c2) (at level 80, right associativity).
Notation "'DONE'" := (Done).
Notation "'NOP'" := (Nop).
(* TODO: check if IF or IFB *)
Notation "'IFB' '{{' bt '}}' '{{' bf '}}'" := (If bt bf) (at level 80, right associativity).
Notation "'LOOP' '{{' body '}}'" := (Loop body) (at level 80, right associativity).
Notation "'DIP' '{{' code '}}'" := (Dip code) (at level 80, right associativity).
Notation "'DROP'" := (Drop).
Notation "'DUP'" := (Dup).
Notation "'SWAP'" := (Swap).
Notation "'PUSH' x" := (Push x) (at level 35).
Notation "'PAIR'" := (Pair).
Notation "'EQ'" := (Eq).
Notation "'NEQ'" := (Neq).
Notation "'LT'" := (Lt).
Notation "'NOT'" := (Not).
Notation "'AND'" := (And).
Notation "'OR'" := (Or).
Notation "'MUL'" := (Mul).
Notation "'ADD'" := (Add).
Notation "'SUB'" := (Sub).
Notation "'LAMBDA' '{{' body '}}'" := (Lambda body) (at level 80, right associativity).
Notation "'DIIP' '{{' code '}}'" := (Dip (Dip code)) (at level 80, right associativity).
Notation "'DIIIP' '{{' code '}}'" := (Dip (Dip (Dip code))) (at level 80, right associativity).
Notation "'IF_SOME' '{{' bt '}}' '{{' bf '}}'" := (If_some bt bf) (at level 80, right associativity).
Notation "'COMPARE'" := (Compare).
Notation "'IFCMPGE' '{{' bt '}}' '{{' bf '}}'" := (Compare;; Ge;; If bt bf) (at level 80, right associativity).
Notation "'CDR'" := (Cdr).
Notation "'CAR'" := (Car).
Notation "'CADR'" := (CAR;; CDR).
Notation "'CDAR'" := (CDR;; CAR).
Notation "'HASH'" := (Hash).
Notation "'GET'" := (Get).
Notation "'FAIL'" := (Fail).
Notation "'CHECK_SIGNATURE'" := (Check_signature).
Notation "'MAP_REDUCE'" := (Map_reduce).
Notation "'TRANSFER_FUNDS'" := (Transfer_funds).

Fixpoint Dup_rec (n : nat) :=
  match n with
    | O => Done
    | 1 => DUP
    | n.+1 => DIP {{ Dup_rec n }} ;; SWAP
  end.

Fixpoint Reduce_rec (lambda : instr) (m : myMap tagged_data tagged_data) :=
match m with
  | [] => Done
  | kv::m => PUSH kv.2;; lambda;; (Reduce_rec lambda m) end
.

Notation "'DUPn' n" := (Dup_rec n) (at level 80).

(* TODO: have a general notation for 'some code between accolades' *)
(* Notation "'IF_SOME' '{{' '}}' '{{' bf '}}'" := (If_some NOP bf) (at level 80, right associativity). *)

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

(* TODO: write instr_type_composition as a function
Fixpoint compose_instr_type (t1 t2 : instr_type) : instr_type := ...
*)

Hint Constructors instr_type_composition.

Reserved Notation "i ':i:' IT" (at level 40).
Reserved Notation "d ':d:' DT" (at level 40).
Inductive has_instr_type : instr -> instr_type -> Prop :=
| IT_Seq : forall i1 i2 Sa Sb Sc Sd Sx Sy,
    i1 :i: (Sa --> Sb) ->
    i2 :i: (Sc --> Sd) ->
    (Sa --> Sb) <o> (Sc --> Sd) === (Sx --> Sy) ->
    (i1 ;; i2) :i: (Sx --> Sy)
| IT_Done :
    DONE :i: ([] --> [])
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
| IT_Pair : forall t1 t2,
    PAIR :i: ([t1 ; t2] --> [ t_pair t1 t2 ])
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
    EQ :i: ([ t_int ] --> [ t_bool ])
| IT_Neq :
    NEQ :i: ([ t_int ] --> [ t_bool ])
| IT_Mul :
    MUL :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Sub :
    SUB :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Lt :
    Lt :i: ([ t_int ] --> [ t_bool ])
| IT_Ge :
    Ge :i: ([ t_int ] --> [ t_bool ])
| IT_Not :
    Not :i: ([ t_bool ] --> [ t_bool ])
| IT_And :
    And :i: ([ t_bool ; t_bool ] --> [ t_bool ])
| IT_Or :
    Or :i: ([ t_bool ; t_bool ] --> [ t_bool ])
| IT_Add :
    Add :i: ([ t_int ; t_int ] --> [ t_int ])
| IT_Lambda : forall b Sb,
    b :i: Sb ->
    Lambda b :i: Sb
| IT_If_Some : forall t Sa Sb bt bf,
    bt :i: (t :: Sa --> Sb) ->
    bf :i: (Sa --> Sb) ->
    If_some bt bf :i: (t_option t :: Sa --> Sb)
| IT_Compare : forall t,
    Compare :i: ([ t ; t ] --> [ t_int ])
| IT_Car : forall t1 t2,
    Car :i: ([ t_pair t1 t2 ] --> [ t1 ])
| IT_Cdr : forall t1 t2,
    Cdr :i: ([ t_pair t1 t2 ] --> [ t2 ])
| IT_Hash : forall t,
    Hash :i: ([ t ] --> [ t_string ])
| IT_Get : forall tk tv,
    Get :i: ([ tk ; t_map tk tv ] --> [ t_option tv ])
| IT_Fail : forall Sa Sb,
    Fail :i: (Sa --> Sb)
| IT_Check_signature :
    Check_signature :i: ([ t_key; t_pair t_signature t_string ] --> [ t_bool ])
| IT_Map_reduce : forall tk tv t,
    Map_reduce :i: ([ t_quotation ([t_pair (t_pair tk tv) t ] --> [ t ]) ; t_map tk tv ; t ] --> [ t ])
(* TODO: is that correct? Anything to ensure on g? *)
| IT_Transfer_funds : forall p r g,
    Transfer_funds :i: ([ p ; t_tez ; t_contract p r ; g ] --> [ r ; g ] )
where "i ':i:' IT" := (has_instr_type i IT)

with has_data_type : tagged_data -> type -> Type :=
| T_bool : forall b, DBool b :d: t_bool
| T_Int : forall z, Int z :d: t_int
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

(*End TypingJudgements.*)
