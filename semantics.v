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
  Require Import language blockchain.

(* TODO: rename all this *)
Definition memory := blockchain.

(* I'm guessing these will be replaced by accesses to memory, with a
precise spec *)
Axiom get_timestamp : unit -> timestamp.
Axiom get_current_amount : unit -> tez.

(* these axioms to model the behavior of Transfer_funds, which I do
not understand as of now *)
Axiom get_new_global : tagged_data -> tagged_data.
Axiom get_return_value : tagged_data -> tagged_data.

Axiom get_le : tagged_data -> bool.
Axiom get_lt : tagged_data -> bool.
Definition get_ge (x : tagged_data) : bool :=
  match x with
    | Int x => (x >= 0)
    | _ => false
  end.

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

Fixpoint step_fun (i : instr) (s : stack) (m : memory) (cur_handle : handle) : option (instr * stack * memory) :=
  match i with
  | Done ;; i2 => Some (i2, s, m)
  | i1 ;; i2 => if step_fun i1 s m cur_handle is Some(i,s',m') then
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
                     match step_fun i1 s m cur_handle with
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
  | Lt => if s is x::s then if is_comparable x then Some(Done,(DBool (get_lt x))::s,m) else None else None
  | Ge => if s is x::s then if is_comparable x then Some(Done,(DBool (get_ge x))::s,m) else None else None
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
  | Check_signature => if s is DKey key:: DPair (DSignature sig) (DString text)::s then Some (Done,DBool (check_signature key sig text) ::s,m) else None
  | Map_reduce => if s is (DLambda lam)::(DMap Map)::x::s then
                    match Reduce_rec lam Map x with
                      | Some(instr,newst) => Some(instr,newst++s,m)
                      | None => None
                    end
                  else
                    None
  | Transfer_tokens => if s is [input;DTez amount;DContract hreceiver;new_storage] then
                         match transfer_tokens input amount cur_handle hreceiver new_storage m with
                           | None => None (* transaction failed) *)
                           | Some (result,m') => Some(DONE,[result;new_storage],m')
                         end
                       else None
  | Exec => if s is x::DLambda f::s then Some(f,x::s,m) else None
  | Create_contract => match s with
                         (* first case: we have an optional delegate *)
                         | kman%dk::(kdel%dk)::(DBool spendable)::(DBool delegatable)::(DTez init_amount)::DLambda code::storage::s =>
                           (* the new pair: handle, new chain *)
                           let hn := create_contract (kman%k) (Some (kdel%k)) spendable delegatable init_amount code storage m in
                           let handle := hn.1 in
                           let new_chain := hn.2 in
                           Some(Done,DContract handle::s,new_chain)
                         (* second case: no delegate *)                        
                         | kman%dk::(DBool spendable)::(DBool delegatable)::(DTez init_amount)::DLambda code::storage::s =>
                           let hn := create_contract (kman%k) None spendable delegatable init_amount code storage m in
                           let handle := hn.1 in
                           let new_chain := hn.2 in
                           Some(Done,DContract handle::s,new_chain)
                         | _ => None
                       end
end.



Lemma step_fun_seq : forall i1 i2 s m h,
  step_fun (i1 ;; i2) s m h =
    if i1 is Done then Some (i2, s, m)
    else if step_fun i1 s m h is Some(i,s',m') then Some(i;;i2,s',m')
    else None.
Proof.
by [].
Qed.


Section Path.

Import Option.

Definition ostep_fun h state :=
  match state with
    | None => None
    | Some(i,s,m) => step_fun i s m h
  end.

Lemma ostep_fun_Done i2 s m h : ostep_fun (ostep_fun h (Some(Done;;i2,s,m))) = ostep_fun (Some(i2,s,m)).
Proof.
by [].
Qed.

Definition evaluate h fuel state := iter fuel (ostep_fun h) state.

Lemma evaluate_1 h st : evaluate h  1 st = ostep_fun h st.
Proof.
by [].
Qed.

Lemma evaluate_S h f st : evaluate h f.+1 st = ostep_fun h (evaluate h f st).
Proof. by rewrite /evaluate; rewrite iterS. Qed.

Lemma evaluate_Sr h f st : evaluate h f.+1 st = (evaluate h f (ostep_fun h st)).
Proof. by rewrite /evaluate; rewrite iterSr. Qed.

Lemma evaluate_None h f : evaluate h f None = None.
Proof. by elim: f => [|f'] => //= -> . Qed.

Definition evaluate_trace h state := traject (ostep_fun h) state.

Definition evaluates h state1 state2 := exists f, evaluate h f state1 = state2.

Lemma eval_comp h : forall f1 f2 st1 st2 st3,
  evaluate h f1 st1 = st2 ->
  evaluate h f2 st2 = st3 ->
  evaluate h (f1 + f2) st1 = st3.
Proof.
elim => [|f1 Hind] f2 st1 st2 st3 .
  by rewrite /=; move ->; rewrite add0n.
rewrite /evaluate.
move => Hev1 Hev2.
by rewrite addnC iter_add Hev1.
Qed.

Lemma ostep_fun_seq h i1 i2 s m :
  ostep_fun h (Some(i1;;i2,s,m)) =
  if i1 is Done then Some(i2,s,m) else
  if ostep_fun h (Some(i1,s,m)) is
  Some(i,s',m') then Some(i;;i2,s',m')
  else None.
Proof.
by case: i1.
Qed.

Lemma evaluates_step_fun h i1 s m:
evaluates h (Some(i1,s,m)) (ostep_fun h (Some(i1,s,m))).
Proof.
by exists 1%N; rewrite evaluate_1.
Qed.

Lemma evaluates_self h st : evaluates h st st.
Proof.
 by exists 0%N.
Qed.

Lemma evaluates_trans h st2 st1 st3 :
  evaluates h st1 st2 ->
  evaluates h st2 st3 ->
  evaluates h st1 st3.
Proof.
move => [f1 Hf1].
move => [f2 Hf2].
exists (f1 + f2)%nat.
move: Hf1 Hf2.
rewrite /evaluate addnC iter_add.
by move => -> ->.
Qed.

Lemma ostep_discr h: forall i1 i2 s m s1 m1,
  ostep_fun h (Some(i1,s,m)) = (Some(i2,s1,m1)) ->
  i1 <> Done.
Proof.
move => i1 i2 s m s1 m1 H1.
destruct i1; simpl ;simpl in H1; congruence.
Qed.

(* This lemma is true but not used currently *)
Lemma ostep_fun_weaken h i1 i1' i2 s s1 m m1 :
  ostep_fun h (Some(i1,s,m)) = (Some(i1',s1,m1)) ->
  (ostep_fun h (Some(i1;;i2,s,m))) = (Some(i1';;i2,s1,m1)).
Proof.
intro H.
generalize (ostep_discr) ; intro Discr.
generalize (Discr _ _ _ _ _ _ _ H); clear Discr.
move => Hi1 /=.
generalize H; clear H.
simpl.
case: (step_fun i1 s m) => [[[i' s' ] m'] |] // [] -> -> -> /=.
by case Hi1 : i1 => // .
Qed.

Lemma evaluates_onestep h st1 st2 :
  evaluates h (ostep_fun h st1) st2 ->
  evaluates h st1 st2.
Proof.
by move => [f Hf]; exists f.+1 ;rewrite evaluate_Sr.
Qed.

Lemma evaluates_weaken h: forall i1 i1' i2 s s1 m m1,
  evaluates h (Some(i1,s,m)) (Some(i1',s1,m1)) ->
  evaluates h (Some(i1;;i2,s,m)) (Some(i1';;i2,s1,m1)).
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
assert (A: exists i3 s3 m3, ostep_fun h (Some (i1, s, m)) = (Some(i3,s3,m3))).

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


case_eq (ostep_fun h (Some (i1, s, m))).
intros.
destruct p as [[a b] c].
exists a, b, c. auto.
intros.

rewrite H0 in H.
rewrite evaluate_None in H. inversion H.
Qed.

Lemma evaluates_seq h i1 i2 i3 s m s1 s2 m1 m2:
  evaluates h (Some(i1,s,m)) (Some(Done,s1,m1)) ->
  evaluates h (Some(i2,s1,m1)) (Some(i3,s2,m2)) ->
  evaluates h (Some(i1;;i2,s,m)) (Some(i3,s2,m2)).
Proof.
move => Hev1 Hev2.
apply: evaluates_trans; last exact: Hev2.
apply: evaluates_trans.
  by apply: evaluates_weaken => //; exact: Hev1.
exact: evaluates_step_fun.
Qed.

Lemma evaluatesEq h st1 st2 : evaluates h st1 st2 <-> exists f, evaluate h f st1 = st2.
Proof.
split => Heval ; last exact: Heval.
  by case: Heval => n; exists n.
Qed.


Lemma evaluates_loop h body s m st x :
  has_data_type x t_bool ->
  evaluates h (Some(Done,s,m)) st ->
  evaluates h (Some(body ;; (Loop body),s,m)) st ->
  evaluates h (Some(Loop body,x::s,m)) st.
Proof.
  move => Htype Hbase Hind.
  inversion Htype; case: b H => _; last first.
  - case: Hbase => f Hbase.
    by exists f.+1; rewrite /evaluate iterSr.
  - case: Hind => f Hind.
    by exists f.+1; rewrite /evaluate iterSr.
Qed.


Lemma evaluates_if h bt bf x s m st :
  has_data_type x t_bool ->
  (x = DBool true -> evaluates h (Some(bt,s,m)) st) ->
  (x = DBool false -> evaluates h (Some(bf,s,m)) st) ->
  evaluates h (Some(If bt bf,x::s,m)) st.
Proof.
move => Htype.
inversion Htype as [b H| |]; case: b H => H H1 H2.
- case: H1 => // => f1 Hev1.
  by exists f1.+1; move: Hev1; rewrite /evaluate iterSr /=.
- case: H2 => // => f2 Hev2.
  by exists f2.+1; move: Hev2; rewrite /evaluate iterSr /=.
Qed.

End Path.
