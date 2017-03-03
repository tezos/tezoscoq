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
  Require Import language.

Axiom memory : Type.

(* I'm guessing these will be replaced by accesses to memory, with a
precise spec *)
Axiom get_timestamp : unit -> timestamp.
Axiom get_current_amount : unit -> tez.

(* these axioms to model the behavior of Transfer_funds, which I do
not understand as of now *)
Axiom get_new_global : tagged_data -> tagged_data.
Axiom get_return_value : tagged_data -> tagged_data.

Axiom get_le : tagged_data -> int.
Axiom get_lt : tagged_data -> int.
Axiom get_ge : tagged_data -> int.

Section Hash.
(* Hash function (sha256, abstracted away here) *)
Axiom hash : forall A :Type, A -> string.
Axiom serialize : tagged_data -> string.

Definition get_hash (x : tagged_data) : tagged_data :=
  DString (hash (serialize x)).

End Hash.

Definition tbool_of_bool (b : bool) : tagged_data :=
  match b with
    | true => DBool true
    | false => DBool false
  end.

Definition get_eq x : tagged_data :=
  match x with
    | Int z => tbool_of_bool (z == 0)
    | _ => DBool false
  end.

Definition get_neq x : tagged_data :=
  match x with
    | Int z => tbool_of_bool (z != 0)
    | _ => DBool false
  end.

Definition get_mul (x : tagged_data) (y : tagged_data) : option tagged_data :=
  match x, y with
    | Int x, Int y => Some (Int (x * y))
    | _, _ => None
  end.

Definition get_add (x : tagged_data) (y : tagged_data) : option tagged_data :=
  match x, y with
    | Int x, Int y => Some (Int (x + y))
    | _, _ => None
  end.

Definition get_sub (x : tagged_data) (y : tagged_data) : option tagged_data :=
  match x, y with
    | Int x, Int y => Some (Int (x - y))
    | _, _ => None
  end.

Definition get_compare x y : option tagged_data :=
  match x,y with
    | Int x, Int y => Some (Int (if x==y then 0 else if (x < y) then -1 else 1))
    | _, _ => None
  end.

(* of course we want something more subtle. We will want an inductive
type for signatures so that checking a signature is boolean equality
to a primitive *)
Definition check_signature (key sig str_to_check :
string) := true.

Fixpoint step_fun (i : instr) (s : stack) (m : memory) : option (instr * stack * memory) :=
  match i with
  | Done ;; i2 => Some (i2, s, m)
  | i1 ;; i2 => if step_fun i1 s m is Some(i,s',m') then
                   Some(i;;i2,s',m')
                 else
                   None
  | Done => None
  | Nop => Some(Done,s,m)
  | If bt bf => if s is x::s then
                 match x with
                   | DBool true => Some(bt,s,m)
                   | DBool false => Some(bf,s,m)
                   | _ => None
                 end else None
  | Loop body => if s is x::s then
                  match x with
                  | DBool true => Some(body ;;(Loop body),s,m)
                  | DBool false => Some(Done,s,m) (* doubtful *) (* is it less doubtful with Done *)
                  | _ => None
                  end else None
  | Dip Done => Some(Done,s,m)
  | Dip i1 => if s is x::s then
                     match step_fun i1 s m with
                       | Some (i2,s',m') => Some(Dip i2,x::s',m')
                       | None => None
                     end else None
  | Drop => if s is x::xs then Some(Done,xs,m) else None
  | Dup => if s is x::xs then Some(Done,x::x::xs,m) else None
  | Swap => if s is x1::x2::s then Some(Done,x2::x1::s,m) else None
  | Push d => Some(Done,d::s,m)
  | Pair => if s is a::b::s then Some(Done,(DPair a b)::s,m) else None
  | Eq => if s is x::s then if is_comparable x then Some(Done,((get_eq x))::s,m) else None else None
  | Neq => if s is x::s then if is_comparable x then Some(Done,((get_neq x))::s,m) else None else None
  | Lt => if s is x::s then if is_comparable x then Some(Done,(Int (get_lt x))::s,m) else None else None
  | Ge => if s is x::s then if is_comparable x then Some(Done,(Int (get_ge x))::s,m) else None else None
  | Not => if s is x::s then match x with
                              | DBool true => Some(Done,DBool false::s,m)
                              | DBool false => Some(Done,DBool true::s,m)
                              | _ => None
                            end else None
  | And => if s is x1::x2::s then
            if (is_bool x1 && is_bool x2) then
              match (x1,x2) with
                | (DBool true,DBool true) => Some(Done,DBool true::s,m)
                | (_,_) => Some(Done,DBool false::s,m)
              end else None
          else None
  | Or => if s is x1::x2::s then
            if (is_bool x1 && is_bool x2) then
              match (x1,x2) with
                | (DBool true,_) => Some(Done,DBool true::s,m)
                | (_,DBool true) => Some(Done,DBool true::s,m)
                | (_,_) => Some(Done,DBool false::s,m)
              end else None
          else None
  | Mul => if s is x1::x2::s then
            match (get_mul x1 x2) with
              | Some(x12) => Some(Done,x12::s,m)
              | None => None
          end else None
  | Sub => if s is x1::x2::s then
            match (get_sub x1 x2) with
              | Some(x12) => Some(Done,x12::s,m)
              | None => None
          end else None
  | Add => if s is x1::x2::s then
            match (get_add x1 x2) with
              | Some(x12) => Some(Done,x12::s,m)
              | None => None
          end else None
  | Lambda code => Some(Done,DLambda code::s,m)
  | If_some bt bf => match s with
                       | DOption (Some v)::s => Some(bt,v::s,m)
                       | DOption (None)::s => Some(bf,s,m)
                       | _ => None
                     end
  | Compare => if s is x1::x2::s then
                 match get_compare x1 x2 with
                   | Some res => Some(Done,res::s,m)
                   | _ => None end
               else
                 None
  | Car => if s is x::s then
             match x with
               | DPair a _ => Some(Done,a::s,m)
               | _ => None
             end
           else None
  | Cdr => if s is x::s then
             match x with
               | DPair _ b => Some(Done,b::s,m)
               | _ => None
             end
           else None
  | Hash => if s is x::s then Some(Done,get_hash x::s,m) else None
  | Get => if s is key::DMap Map::s then
             match get (fun x y => eq_td x y) key Unit Unit Map with
                 | Some res => Some (Done,DOption (Some res)::s,m)
                 | None => Some (Done,(DOption None)::s,m)
             end
           else None
  | Fail => None
  (* :: key : pair signature string : 'S   ->   bool : 'S *)
  | Check_signature => if s is DString key:: DPair (DString sig) (DString str_to_check)::s then Some (Done,DBool (check_signature key sig str_to_check) ::s,m) else None
  | Map_reduce => if s is (DLambda lam)::(DMap Map)::x::s then
                    match Reduce_rec lam Map x with
                      | Some(instr,newst) => Some(instr,newst++s,m)
                      | None => None
                    end
                  else
                    None
  | Transfer_tokens => None
  | Exec => if s is x::DLambda f::s then Some(f,x::s,m) else None
end.



Lemma step_fun_seq : forall i1 i2 s m,
  step_fun (i1 ;; i2) s m =
    if i1 is Done then Some (i2, s, m)
    else if step_fun i1 s m is Some(i,s',m') then Some(i;;i2,s',m')
    else None.
Proof.
by [].
Qed.


Section Path.

Import Option.

Definition ostep_fun state :=
  match state with
    | None => None
    | Some(i,s,m) => step_fun i s m
  end.

Lemma ostep_fun_Done i2 s m : ostep_fun (ostep_fun (Some(Done;;i2,s,m))) = ostep_fun (Some(i2,s,m)).
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

Lemma ostep_fun_seq i1 i2 s m :
  ostep_fun (Some(i1;;i2,s,m)) =
  if i1 is Done then Some(i2,s,m) else
  if ostep_fun (Some(i1,s,m)) is
  Some(i,s',m') then Some(i;;i2,s',m')
  else None.
Proof.
by case: i1.
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

Lemma ostep_discr: forall i1 i2 s m s1 m1,
  ostep_fun (Some(i1,s,m)) = (Some(i2,s1,m1)) ->
  i1 <> Done.
Proof.
move => i1 i2 s m s1 m1 H1.
destruct i1; simpl ;simpl in H1; congruence.
Qed.

(* This lemma is true but not used currently *)
Lemma ostep_fun_weaken i1 i1' i2 s s1 m m1 :
  ostep_fun (Some(i1,s,m)) = (Some(i1',s1,m1)) ->
  (ostep_fun (Some(i1;;i2,s,m))) = (Some(i1';;i2,s1,m1)).
Proof.
intro H.
generalize (ostep_discr) ; intro Discr.
generalize (Discr _ _ _ _ _ _ H); clear Discr.
move => Hi1 /=.
generalize H; clear H.
simpl.
case: (step_fun i1 s m) => [[[i' s' ] m'] |] // [] -> -> -> /=.
by case Hi1 : i1 => // .
Qed.

Lemma evaluates_onestep st1 st2 :
  evaluates (ostep_fun st1) st2 ->
  evaluates st1 st2.
Proof.
by move => [f Hf]; exists f.+1 ;rewrite evaluate_Sr.
Qed.

Lemma evaluates_weaken: forall i1 i1' i2 s s1 m m1,
  evaluates (Some(i1,s,m)) (Some(i1',s1,m1)) ->
  evaluates (Some(i1;;i2,s,m)) (Some(i1';;i2,s1,m1)).
Proof.
intros.
destruct H as [f].
generalize i1 i1' i2 s s1 m m1 H; clear i1 i1' i2 s s1 m m1 H.
induction f.
intros.
simpl in H.
unfold evaluates.
exists O.
simpl. congruence.

intros.
rewrite evaluate_Sr in H.
assert (A: exists i3 s3 m3, ostep_fun (Some (i1, s, m)) = (Some(i3,s3,m3))).

Focus 2.
destruct A as [i3 [s3 [m3 A]]].
rewrite A in H.
generalize (IHf _ _ i2 _ _ _ _ H).
intro B.
destruct B as [g B].
exists g.+1.
rewrite evaluate_Sr.
simpl.
simpl in A. rewrite A.
assert (i1 <> Done).
destruct i1; simpl in A; congruence.
destruct i1; eauto.
congruence.


case_eq (ostep_fun (Some (i1, s, m))).
intros.
destruct p as [[a b] c].
exists a, b, c. auto.
intros.

rewrite H0 in H.
rewrite evaluate_None in H. inversion H.
Qed.

Lemma evaluates_seq i1 i2 i3 s m s1 s2 m1 m2:
  evaluates (Some(i1,s,m)) (Some(Done,s1,m1)) ->
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
  evaluates (Some(Done,s,m)) st ->
  evaluates (Some(body ;; (Loop body),s,m)) st ->
  evaluates (Some(Loop body,x::s,m)) st.
Proof.
  move => Htype Hbase Hind.
  inversion Htype; case: b H => _; last first.
  - case: Hbase => f Hbase.
    by exists f.+1; rewrite /evaluate iterSr.
  - case: Hind => f Hind.
    by exists f.+1; rewrite /evaluate iterSr.
Qed.


Lemma evaluates_if bt bf x s m st :
  has_data_type x t_bool ->
  (x = DBool true -> evaluates (Some(bt,s,m)) st) ->
  (x = DBool false -> evaluates (Some(bf,s,m)) st) ->
  evaluates (Some(If bt bf,x::s,m)) st.
Proof.
move => Htype.
inversion Htype as [b H| |]; case: b H => H H1 H2.
- case: H1 => // => f1 Hev1.
  by exists f1.+1; move: Hev1; rewrite /evaluate iterSr /=.
- case: H2 => // => f2 Hev2.
  by exists f2.+1; move: Hev2; rewrite /evaluate iterSr /=.
Qed.

End Path.
