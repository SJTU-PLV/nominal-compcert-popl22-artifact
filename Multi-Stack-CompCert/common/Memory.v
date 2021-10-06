(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module NMap.
  Definition elt := block.
  Definition elt_eq := eq_block.
  Definition t (A: Type) := block -> A.
  Definition init (A: Type) (v: A) := fun (_: block) => v.
  Definition get (A: Type) (x: block) (m: t A) := m x.
  Definition set (A: Type) (x: block) (v: A) (m: t A) :=
    fun (y: block) => if eq_block y x then v else m y.

  Lemma gi:
    forall (A: Type) (i: elt) (x: A), (init A x) i = x.
Proof.
    intros. reflexivity.
Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set A i x m) i = x.
Proof.
    intros. unfold set. case (eq_block i i); intro.
    reflexivity. tauto.
Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set A j x m) i = m i.
Proof.
    intros. unfold set. case (eq_block i j); intro.
    congruence. reflexivity.
Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get A i (set A j x m) = if elt_eq i j then x else get A i m.
Proof.
    intros. unfold get, set, elt_eq. reflexivity.
Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get A j (set A  i (get A i m) m) = get A j m.
Proof.
    intros. unfold get, set. case (eq_block j i); intro.
    congruence. reflexivity.
Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: block) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
     get B i (map A B f m ) = f(get A i m).
Proof.
    intros. unfold get, map. reflexivity.
Qed.
  Lemma set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
    set A i y (set A i x m) = set A i y m.
Proof.
  intros. apply extensionality.
  intros. unfold set. case (eq_block x0 i); auto.
Qed.
End NMap.

Section STREE.

Fixpoint fresh_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => let m' := fresh_pos tl in
             match plt hd m' with
             |left _ => m'
             |right _ => hd +1
             end
  end.

Lemma Lessthan: forall b l, In b l -> Plt b (fresh_pos l).
Proof.
  intros.
  induction l.
  destruct H.
  destruct H;simpl.
  - destruct (plt a (fresh_pos l)); subst a.
    auto.
    apply Pos.lt_add_r.
  - destruct (plt a (fresh_pos l)); apply IHl in H.
    + auto.
    + eapply Plt_trans. eauto.
      apply Pos.le_nlt in n.

      apply Pos.le_lteq in n. destruct n.
      eapply Plt_trans. eauto.
      apply Pos.lt_add_r.
      subst.
      apply Pos.lt_add_r.
Qed.


Lemma fresh_notin : forall l, ~In (fresh_pos l) l.
Proof.
  intros. intro. apply Lessthan in H.
  unfold fresh_pos in H. extlia.
Qed.

Import List.ListNotations.

Inductive stree : Type :=
  |Node : fid -> (list positive)  -> list stree -> option stree -> stree.

Fixpoint cdepth (t:stree) : nat :=
  match t with
    |Node fid bl tl (Some hd) => S (cdepth hd)
    |Node fid bl tl None => O
  end.

(* well-founded induction *)

Fixpoint depth (t:stree) : nat :=
  match t with
    |Node fid bl tl head =>
     let d_head := option_map depth head in
     let d_list := map depth tl in
     let f := (fun n1 n2 => if Nat.leb n1 n2 then n2 else n1) in
     match d_head with
       |None => fold_right f O d_list + 1
       |Some n => fold_right f n d_list + 1
     end
  end.

Definition substree (t1 t2 : stree) : Prop :=
  match t2 with
    |Node fid bl tl head => head = Some t1 \/ In t1 tl end.

Lemma substree_depth : forall t1 t2, substree t1 t2 ->
                                ((depth t1) < (depth t2))%nat.
Proof.
  intros. unfold substree in H. destruct t2.
  inv H.
  - simpl. induction l0.
    + simpl. lia.
    + simpl. destr. apply Nat.leb_gt in Heqb. lia.
  - induction l0.
    + inv H0.
    + inv H0.
      simpl. repeat destr.
      apply Nat.leb_le in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
      apply Nat.leb_le in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
      apply IHl0 in H. simpl in *.
      repeat destr.
      apply Nat.leb_gt in Heqb. lia.
      apply Nat.leb_gt in Heqb. lia.
Qed.

Lemma substree_wf' : forall n t, (depth t <= n)%nat -> Acc substree t.
  unfold substree; induction n; intros.
  - destruct t.
    destruct o; destruct l0.
    + simpl in H. extlia.
    + simpl in H. extlia.
    + constructor. intros. inv H0; inv H1.
    + simpl in H. extlia.
  - constructor.
    intros.
    apply substree_depth in H0.
    apply IHn. lia.
Defined.

Lemma substree_wf : well_founded substree.
  red; intro. eapply substree_wf'; eauto.
Defined.

Definition stree_ind := well_founded_induction substree_wf.

(* operations *)
Definition empty_stree := Node None [] [] None.

Fixpoint next_stree (t: stree) (id:ident) : (stree * path) :=
  match t with
  | Node b bl l None =>
    let idx := length l in
    ((Node b bl l (Some (Node (Some id) [] [] None))), [idx])
  | Node b bl l (Some t') =>
    let (t'', p) := next_stree t' id in
    (Node b bl l (Some t''), (length l) :: p)
  end.

Fixpoint next_block_stree (t:stree) : (fid * positive * path * stree) :=
  match t with
  |Node b bl l None =>
   (b, (fresh_pos bl), nil, Node b ((fresh_pos bl)::bl) l None)
  |Node b bl l (Some t') =>
   match next_block_stree t' with (pos,path,t'')
    => (pos, (length l)::path, Node b bl l (Some t''))
   end
  end.

Fixpoint return_stree (t: stree) : option (stree * path):=
  match t with
  | Node _ bl l None =>
    None
  | Node b bl l (Some t) =>
    let idx := length l in
    match return_stree t with
    | None => Some ((Node b bl (l ++ [t]) None),[idx])
    | Some (t',p') => Some ((Node b bl l (Some t')),(idx::p'))
    end
  end.

Fixpoint stree_In (fid:option ident)(p:path) (pos:positive) (t:stree) :=
  match p,t with
    |nil , Node b' bl dt _ => fid = b' /\ In pos bl
    |n::p' , Node b' bl dt None =>
     match nth_error dt n with
       |Some t' => stree_In fid p' pos t'
       |None => False
     end
    |n::p',Node b' bl dt (Some t') =>
     if (n =? (length dt))%nat then stree_In fid p' pos t' else
     match nth_error dt n with
       |Some t'' => stree_In fid p' pos t''
       |None => False
     end
  end.

Lemma node_Indec :
  forall (f f0:fid) (p:positive) (l: list positive), {f=f0 /\ In p l}+{~(f=f0/\ In p l)}.
Proof.
  intros.
  destruct (fid_eq f f0) eqn:?.
  destruct (In_dec peq p l).
  subst. auto.
  right. intro. inv H. congruence.
  right. intro. inv H. congruence.
Qed.

(* properties of the operations above *)

Definition cpath (s:stree) : path :=
  match next_block_stree s with
    |(f,pos,path,_) => path
  end.

Definition npath (s:stree)(id:ident) : path :=
  let (t,p) := next_stree s id in p.

Lemma next_stree_cdepth: forall p t t' id,
    next_stree t id = (t',p) -> cdepth t' = S (cdepth t).
Proof.
  induction p; (intros; destruct t; destruct o; simpl in H).
  destr_in H. inv H. destr_in H. inv H.
  simpl. exploit IHp; eauto. inv H. simpl. auto.
Qed.

Lemma next_block_stree_cdepth : forall p pos fid t t',
    next_block_stree t = (fid,pos,p,t') -> cdepth t' = cdepth t.
Proof.
  induction p; (intros; destruct t; destruct o; inv H; repeat destr_in H1).
  auto. simpl. exploit IHp; eauto.
Qed.

Lemma return_stree_cdepth : forall p t t',
    return_stree t = Some (t',p) -> S (cdepth t') = (cdepth t).
Proof.
  induction p; (intros; destruct t; destruct o; inv H; repeat destr_in H1).
  simpl. exploit IHp; eauto. simpl. destruct s. destruct o.
  simpl in Heqo. repeat destr_in Heqo. reflexivity.
Qed.

Lemma next_stree_cpath :
  forall p t t' id,
    next_stree t id = (t',p) ->  cpath t' = p.
Proof.
  induction p.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s id). inv H.
    simpl in H. inv H.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s id) eqn:?. inv H.
    apply IHp in Heqp0.
    unfold cpath in *. simpl in *.
    destruct (next_block_stree s0) eqn:?.
    destruct p0 eqn:?.
    destruct p1 eqn:?.
    congruence. simpl in H. inv H.
    unfold cpath. simpl. auto.
Qed.

Lemma next_stree_next_block_stree :
  forall t t' t'' id p f pos path,
    next_stree t id = (t',p) ->
    next_block_stree t' = (f,pos,path,t'') ->
    f = Some id /\ pos = 1%positive /\ path = p.
Proof.
  induction t using stree_ind. intros. destruct t. destruct o.
  - simpl in H0. destruct (next_stree s id) eqn:?. inv H0. simpl in H1.
    destruct (next_block_stree s0) eqn:?. destruct p. destruct p.
    exploit H. instantiate (1:=s). simpl. auto. eauto. eauto. inv H1.
    intros [A [B C]]. split. auto. split. auto. congruence.
  - simpl in H0. inv H0. simpl in H1. inv H1. auto.
Qed.

Lemma next_block_stree_next_block : forall s1 s2 s3 fid1 fid2 pos1 pos2 path1 path2,
      next_block_stree s1 = (fid1,pos1,path1,s2) ->
      next_block_stree s2 = (fid2,pos2,path2,s3) ->
      fid1 = fid2 /\ path1 = path2 /\ pos2 = Pos.succ pos1.
Proof.
  induction s1 using stree_ind. intros. destruct s1. destruct o.
  - simpl in H0. destruct (next_block_stree s) eqn:?. destruct p. destruct p.
    inv H0. simpl in H1.
    destruct (next_block_stree s0) eqn:?. destruct p. destruct p. inv H1.
    exploit H. instantiate (1:=s). simpl. auto. eauto. eauto.
    intros [A [B C]]. split. auto. split. rewrite B. auto. auto.
  - simpl in H0. inv H0. simpl in H1. inv H1. split. auto.
    split. auto. rewrite pred_dec_false. lia. extlia.
Qed.

Definition stree_Indec :forall tree f path p , {stree_In f path p tree}+{~stree_In f path p tree}.
Proof.
  induction tree using (well_founded_induction substree_wf ); intros.
  destruct tree; destruct path.
  - simpl. apply node_Indec.
  - destruct o; destruct l0; simpl; repeat destr.
    + apply H. simpl. auto.
    + rewrite nth_error_nil in Heqo. congruence.
    + apply H. simpl. auto.
    + apply nth_error_in in Heqo.
      apply H. simpl. auto.
    + rewrite nth_error_nil in Heqo. congruence.
    + apply nth_error_in in Heqo.
      apply H. simpl. auto.
Qed.

Lemma stree_freshness : forall b p pos t t', next_block_stree t = (b,pos,p,t')
  -> ~ stree_In b p pos t.
Proof.
  induction p.
  - intros. destruct t. simpl in *.
    destruct o.
    destruct (next_block_stree s).
    destruct p. inv H.
    inv H.
    intro. inv H. apply fresh_notin in H1. auto.
  - intros. destruct t. simpl in *.
    destruct o.
    destruct (next_block_stree s) eqn:?.
    destruct p0. inv H.
    rewrite <- beq_nat_refl. eauto.
    inv H.
Qed.

Lemma next_block_stree_in : forall t t' path pos path' pos' f f',
        next_block_stree t = (f,pos,path,t') ->
        stree_In f' path' pos' t' <->
        ((f',path',pos') = (f,path,pos)
        \/ stree_In f' path' pos' t).
Proof.
  induction t using stree_ind. intros.
  destruct t.
  - destruct path; destruct path';
    simpl in H0; repeat destr_in H0; simpl.
    + split; intros; inv H0.
      inv H2; auto.
      inv H1; auto. inv H1; auto.
    + split; intros; auto.
      destruct H0. inv H0. auto.
    + split; intros; auto.
      destruct H0. inv H0. auto.
    + destr.
      *
      apply beq_nat_true in Heqb. subst.
      exploit H; eauto. simpl. auto.
      intros.
      split; intros. apply H0 in H1.
      inv H1. left. inv H2. auto.
      right. auto.
      apply H0. inv H1. inv H2. auto.
      auto.
      *
      apply beq_nat_false in Heqb.
      destr.
Qed.

Lemma next_stree_in : forall p p' t t' pos b id,
    next_stree t id = (t',p') ->
    stree_In b p pos t <-> stree_In b p pos t'.
Proof.
  induction p.
  - intros. destruct t. destruct o.
    simpl in H. destruct (next_stree s). inv H.
    simpl. reflexivity.
    simpl in H. inv H.
    simpl. reflexivity.
  - intros. destruct t. destruct o.
    * simpl in H. destruct (next_stree s) eqn:?. inv H.
      eapply IHp in Heqp0.
      simpl.
      destruct (a =? Datatypes.length l0)%nat. eauto.
      destruct (nth_error l0 a). reflexivity. split; auto.
    * simpl in H. inv H. simpl.
      destruct (a =? Datatypes.length l0)%nat eqn:H.
      assert (nth_error l0 a = None).
      apply nth_error_None. apply beq_nat_true in H.
      subst. lia. rewrite H0. destruct p.
      simpl. split. intro. inv H1. intros [H1 H2]. congruence.
      simpl. destruct n; reflexivity.
      destruct (nth_error l0 a); reflexivity.
Qed.

Lemma return_stree_in : forall s s' path p pos b,
    return_stree s = Some (s',path) ->
    stree_In b p pos s <-> stree_In b p pos s'.
Proof.
  induction s using stree_ind. intros.
  destruct s. destruct o.
  - simpl in H0. repeat destr_in H0;
    destruct p; simpl. reflexivity.
    destr. eapply H; eauto. simpl. auto. reflexivity.
    destr. apply beq_nat_true in Heqb0. subst.
    rewrite nth_error_app2. rewrite Nat.sub_diag.
    reflexivity. lia.
    apply beq_nat_false in Heqb0.
    destruct (n <? Datatypes.length l0)%nat eqn:H1.
    rewrite nth_error_app1. destr; auto.
    apply Nat.ltb_lt. auto.
    apply Nat.ltb_ge in H1.
    assert (nth_error (l0++[s]) n = None).
    apply nth_error_None.
    rewrite app_length. simpl. lia. rewrite H0.
    assert (nth_error l0 n = None).
    apply nth_error_None. lia. rewrite H2.
    reflexivity.
  - inv H0.
Qed.

(* sp from stree *)

Fixpoint top_sp' (st:stree): fid * path :=
  match st with
    |Node f bl l (Some t') =>
     let (fid,path) := top_sp' t' in
     (fid, (Datatypes.length l)::path)
    |Node f bl l None => (f,[])
  end.

Fixpoint parent_sp' (st:stree) : option (fid * path) :=
  match st with
    |Node f bl l (Some st') =>
     let idx := Datatypes.length l in
     match parent_sp' st' with
       |Some (fid,path) => Some (fid,idx::path)
       |None => Some (f,[])
     end
    |Node f bl l None => None
  end.

Inductive struct_eq : stree -> stree -> Prop :=
  |struct_eq_leaf : forall fi bl1 bl2,
      struct_eq (Node fi bl1 nil None) (Node fi bl2 nil None)
  |struct_eq_dead_node :
     forall fi bl1 bl2 tl1 tl2,
       list_forall2 struct_eq tl1 tl2 ->
       struct_eq (Node fi bl1 tl1 None) (Node fi bl2 tl2 None)
  |struct_eq_active_node :
     forall fi bl1 bl2 tl1 tl2 head1 head2,
       list_forall2 struct_eq tl1 tl2 ->
       struct_eq head1 head2 ->
       struct_eq (Node fi bl1 tl1 (Some head1)) (Node fi bl2 tl2 (Some head2)).

Theorem struct_eq_refl : forall s , struct_eq s s.
Proof.
  induction s using stree_ind.
  intros. destruct s.
  destruct o; destruct l0.
  - apply struct_eq_active_node. constructor.
    apply H. simpl. left. auto.
  - apply struct_eq_active_node.
    {
      constructor. apply H. simpl. auto.
      induction l0. constructor.
      constructor. apply H. simpl. auto.
      apply IHl0. intros. apply H.
      simpl in H0. simpl. inv H0. auto. inv H1; auto.
    }
    apply H. simpl. auto.
  - constructor.
  - apply struct_eq_dead_node.
    constructor. apply H. simpl. auto.
    induction l0. constructor.
    constructor. apply H. simpl. auto.
    apply IHl0. intros.
    apply H. simpl. simpl in H0.
    destruct H0. inv H0. destruct H0; auto.
Qed.

Lemma list_forall2_struct_eq_refl : forall l,
    list_forall2 struct_eq l l.
Proof.
  induction l; constructor.
  apply struct_eq_refl. auto.
Qed.

Theorem struct_eq_comm : forall s1 s2, struct_eq s1 s2 -> struct_eq s2 s1.
Proof.
  induction s1 using stree_ind.
  intros. inv H0.
  constructor.
  constructor.
   eapply list_forall2_ind with (P:= fun t1 t2 => In t1 tl1 /\ struct_eq t1 t2) (P0:= fun l1 l2 => list_forall2 struct_eq l2 l1 ).
   constructor.
   intros. inv H0. constructor; auto. apply H. simpl. auto. auto.
   eapply list_forall2_imply; eauto.
  constructor.
   eapply list_forall2_ind with (P:= fun t1 t2 => In t1 tl1 /\ struct_eq t1 t2) (P0:= fun l1 l2 => list_forall2 struct_eq l2 l1 ).
   constructor.
   intros. inv H0. constructor; auto. apply H. simpl. auto. auto.
   eapply list_forall2_imply; eauto.
   apply H. simpl. auto. auto.
Qed.

Theorem list_forall2_trans : forall {A:Type} (l2 l1 l3 : list A) (P: A -> A -> Prop),
    (forall a1 a2 a3, In a1 l1 -> P a1 a2 -> P a2 a3 -> P a1 a3) ->
    list_forall2 P l1 l2 ->
    list_forall2 P l2 l3 ->
    list_forall2 P l1 l3.
Proof.
  induction l2; intros; inv H0; inv H1; constructor.
  eapply H. left. auto. all: eauto.
  eapply IHl2. intros. exploit H. right. eauto. all: eauto.
Qed.

Theorem struct_eq_trans : forall s1 s2 s3, struct_eq s1 s2 -> struct_eq s2 s3 -> struct_eq s1 s3.
Proof.
  induction s1 using stree_ind.
  intros. inv H0. inv H1.
  - constructor.
  - inv H5. constructor.
  - destruct s3. inv H1. inv H2. constructor.
    constructor.
    eapply list_forall2_trans.
    intros. eapply H. simpl. auto. all : eauto.
  - destruct s3. inv H1. inv H2. constructor. inv H5. constructor.
    eapply H; eauto. simpl. auto.
    constructor. inv H5. constructor. eapply H; eauto. simpl. auto.
    eapply list_forall2_trans.
    intros. eapply H. simpl. auto. all : eauto.
    eapply H; eauto. simpl. auto.
Qed.

Lemma next_block_stree_struct_eq: forall s path s' f pos,
    next_block_stree s = (f,pos,path,s') -> struct_eq s s'.
Proof.
  induction s. intros. destruct s. destruct s'.
  inv H0. destr_in H2.
  destruct (next_block_stree s) eqn:?.
  destruct p. inv H2.
  constructor. apply list_forall2_struct_eq_refl.
  eapply H; eauto. simpl. auto.
  inv H2. constructor. apply list_forall2_struct_eq_refl.
Qed.


Definition is_active (s:stree) : Prop :=
  match s with
    |Node _ _ _ (Some _) => True
    |_ => False
  end.

Lemma active_struct_eq : forall s1 s2,
    struct_eq s1 s2 ->
    is_active s1 <-> is_active s2.
Proof.
  intros. inv H; reflexivity.
Qed.

Lemma next_stree_struct_eq: forall s1 s2 id p1 p2 s1' s2',
    struct_eq s1 s2 ->
    next_stree s1 id = (s1',p1) ->
    next_stree s2 id = (s2',p2) ->
    p1 = p2 /\ struct_eq s1' s2'.
Proof.
  induction s1. intros.
  destruct s1; destruct s2. inv H0.
  - inv H1. inv H2. split. auto. constructor. constructor. constructor.
  - inv H1. inv H2. split.
    apply list_forall2_length in H4. congruence.
    constructor. auto. constructor.
  - inv H1. inv H2. destr_in H3. destr_in H1.
    inv H3. inv H1.
    apply list_forall2_length in H5 as H6.
    exploit H; eauto. simpl. auto. intros [H1 H2].
    split. congruence. constructor. auto. auto.
Qed.

Lemma return_stree_struct_eq: forall s1 s2 s1' p,
    struct_eq s1 s2 ->
    return_stree s1 = Some (s1',p) ->
    exists s2',
    return_stree s2 = Some (s2',p) /\
    struct_eq s1' s2'.
Proof.
  induction s1. intros.
  destruct s1; destruct s2. inv H0; inv H1.
  repeat destr_in H2.
  + exploit H; eauto. simpl. auto. intros (head2' & H5 & H6).
    exists (Node f0 l1 l2 (Some head2')). split. simpl. rewrite H5.
    apply list_forall2_length in H4 as H7. rewrite H7. auto.
    constructor. auto. auto.
  + exists (Node f0 l1 (l2++[head2]) None). split.
    simpl. destruct head1. inv Heqo. repeat destr_in H1.
    inv H11. simpl. apply list_forall2_length in H4 as H7. rewrite H7. auto.
    simpl. apply list_forall2_length in H4 as H7. rewrite H7. auto.
    constructor. apply list_forall2_app. auto.
    constructor. auto. constructor.
Qed.

Lemma struct_eq_next_block_stree : forall s1 s2 fid1 fid2 p1 p2 pos1 pos2 s1' s2',
    struct_eq s1 s2 ->
    next_block_stree s1 = (fid1,pos1,p1,s1') ->
    next_block_stree s2 = (fid2,pos2,p2,s2') ->
    fid1=fid2 /\ p1 = p2.
Proof.
  induction s1. intros.
  destruct s1. destruct s2. inv H0.
  - inv H1. inv H2. auto.
  - inv H1. inv H2. auto.
  - inv H1. inv H2.  repeat destr_in H3.  repeat destr_in H1.
    exploit H; eauto. simpl. auto. intros [X Y].
    split. auto. subst. erewrite list_forall2_length; eauto.
Qed.

End STREE.

Section STACKADT.

Record frame : Type :=
  {
    frame_size : Z;
    frame_size_pos:
      (0 <= frame_size)%Z;
  }.

Definition mk_frame (sz:Z) :=
  {|
   frame_size := Z.max 0 sz;
   frame_size_pos := Z.le_max_l _ _
  |}.

Definition stage := list frame.

Definition frame_size_a (f:frame) : Z :=
  align (frame_size f) 8.

Fixpoint size_of_all_frames (t:stage) : Z :=
  match t with
    |nil => 0
    |hd :: tl => (frame_size_a hd) + size_of_all_frames tl
  end.
(*
Definition size_of_head_frame (t:stage) : Z :=
  match t with
    |nil => 0
    |hd::tl => (frame_size hd)
  end.
*)
Definition stackadt := list stage.

Fixpoint stack_size (s:stackadt): Z :=
  match s with
    |nil => 0
    |hd::tl => size_of_all_frames hd + stack_size tl
  end.

Lemma stack_size_app : forall s1 s2,
    stack_size (s1++s2) = stack_size s1 + stack_size s2.
Proof.
  intros. induction s1. auto. simpl. lia.
Qed.

Lemma frame_size_a_pos : forall f,
  ( 0<= frame_size_a f)%Z.
Proof.
  intros. generalize (frame_size_pos f). intro.
  unfold frame_size_a.
  generalize (align_le (frame_size f) 8). intro.
  assert (8>0) by lia. apply H0 in H1. lia.
Qed.

Lemma size_of_all_frames_pos:
  forall t,
    (0 <= size_of_all_frames t)%Z.
Proof.
  intros. induction t.
  simpl. lia.
  simpl. generalize (frame_size_a_pos a). intro. lia.
Qed.

Lemma stack_size_pos:
  forall s,
    (0 <= stack_size s)%Z.
Proof.
  induction s; simpl; intros; eauto. lia.
  generalize (size_of_all_frames_pos a); lia.
Qed.

Lemma stack_size_tl:
  forall l,
    (stack_size (tl l) <= stack_size l)%Z.
Proof.
  induction l; simpl; intros. lia.
  generalize (size_of_all_frames_pos a); lia.
Qed.

Definition max_stacksize : Z := 4096.
End STACKADT.

Parameter thread_id : nat.
(* Declare Module Sup: SUP. *)

Module Sup <: SUP.

Record sup' : Type := mksup {
  stacks : list stree;
  astacks : list stackadt;
  global : list ident;

  sid : nat;

  sid_valid : (length stacks > sid)%nat;
  length_eq : length stacks = length astacks
}.

Definition sup := sup'.

Definition tid := thread_id.

Program Definition sup_init : sup :=
  mksup (list_repeat (S tid) empty_stree) (list_repeat (S tid) nil) nil tid _ _.
Next Obligation.
  rewrite length_list_repeat. lia.
Qed.
Next Obligation.
  repeat rewrite length_list_repeat. lia.
Qed.

Lemma mksup_ext : forall ss1 ss2 as1 as2 g1 g2 id1 id2 a1 a2 b1 b2,
    ss1 = ss2 -> as1 = as2 -> g1 = g2 -> id1 = id2 ->
    mksup ss1 as1 g1 id1 a1 b1 = mksup ss2 as2 g2 id2 a2 b2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

Definition stack (s:sup) := nth (sid s) (stacks s) empty_stree.

Fixpoint setstack (l: list stree) (t:stree) (id:nat): list stree :=
  match id with
    |O => match l with
           |nil => l
           |a :: l' => t :: l'
         end
    |S n => match l with
             |nil => l
             |a :: l' => a :: (setstack l' t n)
           end
end.

Lemma setstack_length : forall n t l,
    length (setstack l t n) = length l.
Proof.
  induction n; intros.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
Qed.

Lemma setstack_stack:
  forall n l a,
    (n < length l)%nat ->
    nth n (setstack l a n) empty_stree = a.
Proof.
  induction n; intros; simpl.
  - destruct l; simpl in *. extlia. auto.
  - destruct l; simpl in *. extlia. apply IHn. lia.
Qed.


Definition astack (s:sup) := nth (sid s)(astacks s) nil.

Fixpoint setastack (l: list stackadt) (t:stackadt) (id:nat): list stackadt :=
  match id with
    |O => match l with
           |nil => l
           |a :: l' => t :: l'
         end
    |S n => match l with
             |nil => l
             |a :: l' => a :: (setastack l' t n)
           end
end.

Lemma setastack_length : forall n t l,
    length (setastack l t n) = length l.
Proof.
  induction n; intros.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
Qed.

Lemma setastack_astack:
  forall n l a,
    (n < length l)%nat ->
    nth n (setastack l a n) nil = a.
Proof.
  induction n; intros; simpl.
  - destruct l; simpl in *. extlia. auto.
  - destruct l; simpl in *. extlia. apply IHn. lia.
Qed.

Lemma list_repeat_in {A:Type} (n:nat)(a b:A):
  nth n (list_repeat (S n) a) b = a.
Proof.
  induction n. simpl. auto.
  simpl. destruct n. auto.  eauto.
Qed.

Theorem  sup_init_sid : sid sup_init = tid.
Proof. reflexivity. Qed.

Theorem sup_init_stack: stack sup_init = empty_stree.
Proof.
  unfold stack. rewrite sup_init_sid. unfold sup_init.
  Opaque list_repeat. simpl. rewrite list_repeat_in. auto.
Qed.

Theorem sup_init_astack: astack sup_init = nil.
Proof.
  unfold astack. rewrite sup_init_sid. unfold sup_init.
  Opaque list_repeat. simpl. rewrite list_repeat_in. auto.
Qed.

Theorem sup_init_global: global sup_init = nil.
Proof. reflexivity. Qed.

Definition sup_cpath (s:sup) := cpath (stack s).

Definition sup_npath (s:sup) := npath (stack s).

Definition sup_depth (s:sup) := depth (stack s).

Definition sup_In(b:block)(s:sup) : Prop :=
  match b with
  | Stack n fid path pos => if (n=?(sid s))%nat then stree_In fid path pos (stack s) else False
  | Global id => In id (global s)
  end.

Definition empty_in: forall b, ~ sup_In b sup_init.
Proof.
  intros. destruct b; simpl in *; try congruence.
  destr. rewrite sup_init_stack. intro. destruct p; simpl in H.
  inv H. inv H1. destruct n0; simpl in H. inv H. inv H.
Qed.

Definition sup_dec : forall b s, {sup_In b s}+{~sup_In b s}.
Proof.
  intros. destruct b. simpl. destr.
  apply stree_Indec.
  apply In_dec. apply peq.
Qed.

Definition fresh_block (s:sup): block :=
  match next_block_stree (stack s) with
    |(f,pos,path,_) =>  Stack (sid s) f path pos
  end.

Theorem freshness : forall s, ~sup_In (fresh_block s) s.
Proof.
  intros. unfold fresh_block.
  destruct (next_block_stree (stack s)) eqn:?.
  destruct p. destruct p. simpl. destr.
  eapply stree_freshness; eauto.
Qed.

Program Definition sup_incr (s:sup):sup :=
  let (pp,t') := next_block_stree (stack s) in
  mksup (setstack (stacks s) t' (sid s)) (astacks s) (global s) (sid s) _ _.
Next Obligation.
  rewrite setstack_length. apply sid_valid.
Qed.
Next Obligation.
  rewrite setstack_length. apply length_eq.
Qed.

Theorem sup_incr_in : forall b s,
    sup_In b (sup_incr s) <-> b = (fresh_block s) \/ sup_In b s.
Proof.
  intros. unfold sup_In. destruct b.
  - unfold sup_incr. unfold fresh_block.
    destruct (next_block_stree (stack s)) eqn:?. simpl.
    destruct p1. destruct p1. unfold stack. simpl.
    rewrite setstack_stack. 2: apply sid_valid. destr.
    apply Nat.eqb_eq in Heqb. subst.
    eapply next_block_stree_in in Heqp1.
    split. intro. apply Heqp1 in H. destruct H.
    inv H. auto. auto.
    intro. apply Heqp1. destruct H.
    inv H. auto. auto.
    apply Nat.eqb_neq in Heqb.
    split. auto. intros [H|H]. congruence. auto.
  - unfold sup_incr. unfold fresh_block.
    destruct (next_block_stree) eqn:?. simpl.
    destruct p. destruct p. split.
    auto. intros [H|H]. inv H. auto.
Qed.

Definition sup_include(s1 s2:sup) := forall b, sup_In b s1 -> sup_In b s2.

Theorem sup_incr_in1 : forall s, sup_In (fresh_block s) (sup_incr s).
Proof. intros. apply sup_incr_in. left. auto. Qed.
Theorem sup_incr_in2 : forall s, sup_include s (sup_incr s).
Proof. intros. intro. intro. apply sup_incr_in. right. auto. Qed.

Lemma astack_sup_incr : forall s,
  astack (sup_incr s) = astack s.
Proof.
  intros. unfold sup_incr. destr.
Qed.

Lemma sup_include_refl : forall s:sup, sup_include s s.
Proof. intro. intro. auto. Qed.

Lemma sup_include_trans:
  forall p q r:sup,sup_include p q-> sup_include q r -> sup_include p r.
Proof.
  intros. intro. intro.  auto.
Qed.

Lemma sup_include_incr:
  forall s, sup_include s (sup_incr s).
Proof.
  intros. apply sup_incr_in2.
Qed.

(* sup_incr_frame *)
Program Definition sup_incr_frame (s:sup)(id:ident):sup :=
  let (t',p) := next_stree (stack s) id in
  mksup (setstack (stacks s) t' (sid s)) (astacks s) (global s) (sid s) _ _.
Next Obligation.
  rewrite setstack_length. apply sid_valid.
Qed.
Next Obligation.
  rewrite setstack_length. apply length_eq.
Qed.

Theorem sup_incr_frame_in : forall s b id,
    sup_In b s <-> sup_In b (sup_incr_frame s id).
Proof.
  intros. unfold sup_In. destruct b.
  - unfold sup_incr_frame.
    destruct (next_stree (stack s)) eqn:?.
    simpl. unfold stack. simpl. rewrite setstack_stack. 2: apply sid_valid.
    destr. eapply next_stree_in. eauto.
  - unfold sup_incr_frame.
    destruct (next_stree (stack s)).
    reflexivity.
Qed.

Lemma astack_sup_incr_frame : forall s id,
  astack (sup_incr_frame s id) = astack s.
Proof.
  intros. unfold sup_incr_frame. destr.
Qed.

(* sup_return_frame *)
Program Definition sup_return_frame (s:sup) : option sup :=
  match return_stree (stack s) with
    |Some (t',p) => Some (mksup (setstack (stacks s) t' (sid s)) (astacks s) (global s) (sid s) _ _)
    |None => None
  end.
Next Obligation.
  rewrite setstack_length. apply sid_valid.
Qed.
Next Obligation.
  rewrite setstack_length. apply length_eq.
Qed.

Definition sup_return_frame' (s:sup) : sup :=
  match sup_return_frame s with
    |Some s' => s'
    |None => sup_init
  end.

Lemma sup_return_refl : forall s s', is_active (stack s) ->
    sup_return_frame s = Some s' <-> sup_return_frame' s = s'.
Proof.
  intros.
  unfold sup_return_frame'. destruct (sup_return_frame s) eqn:?.
  split;  congruence.
  unfold sup_return_frame in Heqo.
  destruct (return_stree (stack s)) eqn:?. destruct p.
  inv Heqo.
  unfold is_active in H. destruct (stack s).
  destruct o.
  inv Heqo0. destr_in H1. destruct p. inv H1.
  destruct H.
Qed.

Lemma sup_return_refl' : forall s , is_active (stack s) ->
    sup_return_frame s = Some (sup_return_frame' s).
Proof.
  intros. apply sup_return_refl; auto.
Qed.

Theorem sup_return_frame_in : forall s s',
    sup_return_frame s = Some (s') ->
    (forall b, sup_In b s <-> sup_In b s').
Proof.
  intros.
  destruct b; unfold sup_return_frame in H;
  destruct (return_stree (stack s)) eqn:?.
  - destruct p1. inv H. simpl. destr.
    eapply return_stree_in; eauto. unfold stack in *. simpl.
    rewrite setstack_stack. eauto. apply sid_valid.
  - inv H.
  - destruct p. inv H. reflexivity.
  - inv H.
Qed.

(* sup_incr_glob *)
Program Definition sup_incr_glob (i:ident) (s:sup) : sup :=
 mksup (stacks s) (astacks s)(i::(global s)) (sid s) _ _.
Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  apply length_eq.
Qed.

Theorem sup_incr_glob_in :  forall i s b,
    sup_In b (sup_incr_glob i s) <-> b = (Global i) \/ sup_In b s.
Proof.
  split.
  - unfold sup_incr_glob.
    destruct b; simpl. auto. intros [H|H]. rewrite H. auto. auto.
  - intros [H|H]; unfold sup_incr_glob.
    rewrite H. simpl. auto.
    destruct b. simpl. auto. simpl. auto.
Qed.

Theorem sup_incr_glob_in1 : forall i s, sup_In (Global i) (sup_incr_glob i s).
Proof. intros. apply sup_incr_glob_in. left. auto. Qed.
Theorem sup_incr_glob_in2 : forall i s, sup_include s (sup_incr_glob i s).
Proof. intros. intro. intro. apply sup_incr_glob_in. right. auto. Qed.

(* sup_incr_stack *)

Definition sup_incr_block := sup_incr.

(* about stackadt *)

Program Definition sup_push_stage (s:sup) :=
  mksup (stacks s) (setastack (astacks s) (nil::(astack s)) (sid s)) (global s) (sid s) _ _.
Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  rewrite setastack_length. apply length_eq.
Qed.

Program Definition sup_record_frame (f:frame)(s:sup) : option sup:=
  match (astack s) with
    |nil => None
    |hd::tl => Some(mksup (stacks s)
                         (setastack (astacks s) ((f::hd)::tl) (sid s))
                         (global s) (sid s) _ _)
  end.
Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  rewrite setastack_length. apply length_eq.
Qed.

Program Definition sup_pop_stage (s:sup) :=
  match (astack s) with
  |nil => None
  |hd::tl => Some(mksup (stacks s)
                       (setastack (astacks s) (tl) (sid s))
                       (global s) (sid s) _ _)
  end.
Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  rewrite setastack_length. apply length_eq.
Qed.
(*
Theorem sup_push_stage_stack : forall s, stack s = stack (sup_push_stage s).
Proof.
  intros. unfold sup_push_stage. reflexivity. Qed.

Theorem sup_push_stage_global : forall s, global s = global (sup_push_stage s).
Proof.
  intros. unfold sup_push_stage. reflexivity. Qed.

Theorem sup_record_frame_stack :forall sz s s', sup_record_frame sz s = Some s' -> stack s = stack s'.
Proof.
  intros. unfold sup_record_frame in H. destruct (astack s). discriminate. simpl in H. inv H.  reflexivity.
Qed.

Theorem sup_record_frame_global :forall sz s s', sup_record_frame sz s = Some s' -> stack s = stack s'.
Proof.
  intros. unfold sup_record_frame in H. destruct (astack s). discriminate. simpl in H. inv H.  reflexivity.
Qed.

Theorem sup_pop_stage_supp : forall s s', sup_pop_stage s = Some s' -> supp s = supp s'.
Proof.
  intros. unfold sup_pop_stage in H.  destruct (stack s); auto. discriminate.
  inv H. reflexivity.
Qed.
*)
End Sup.

Module Mem <: MEM.
Include Sup.
Local Notation "a # b" := (NMap.get _ b a) (at level 1).

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Record mem' : Type := mkmem {
  mem_contents: NMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: NMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  support: sup;

  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(sup_In b support) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst (mem_contents#b) = Undef
}.

Definition mem := mem'.

Definition nextblock (m:mem) := fresh_block (support m).

Definition sdepth (m:mem) := cdepth (stack (support m)).

Lemma sdepth_active : forall m, sdepth m <> O -> is_active (stack (support m)).
Proof.
  intros. unfold sdepth in H. simpl in H.
  destruct (stack (support m)). destruct o; simpl in *.
  auto. extlia.
Qed.

Lemma nextblock_stack : forall m, exists f path pos,
      nextblock m = Stack (sid (support m)) f path pos.
Proof.
  intros. unfold nextblock. unfold fresh_block.
  destruct (next_block_stree (stack (support m))).
  destruct p. destruct p.
  eauto.
Qed.

Definition stackeq (m1 m2: mem) : Prop :=
  stack (support m1) = stack (support m2) /\ sid (support m1) = sid (support m2).

Lemma stackeq_nextblock : forall m1 m2,
    stackeq m1 m2  ->
    nextblock m1 = nextblock m2.
Proof.
  intros. inv H. unfold nextblock. unfold fresh_block.
  rewrite H0. repeat destr.
Qed.

Definition empty_stack (m:mem) : Prop :=
  match stack (support m) with
    |Node _ _ _ None => True
    |_ => False
  end.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 sup1 sup2 a1 a2 b1 b2 c1 c2,
  cont1=cont2 -> acc1=acc2 -> sup1=sup2 ->
  mkmem cont1 acc1 sup1 a1 b1 c1= mkmem cont2 acc2 sup2 a2 b2 c2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := sup_In b (support m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (sup_dec b m.(support)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. lia.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. lia.
  right; red; intros. elim n. red; intros; apply H0; lia.
  right; red; intros. elim n. apply H0. lia.
  left; red; intros. extlia.
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). lia.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by lia. auto.
  simpl. apply Z.divide_1_l.
  destruct H. apply H. simpl. lia.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (NMap.init _ (ZMap.init Undef))
        (NMap.init _ (fun ofs k => None))
        sup_init  _ _ _.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)
Lemma mem_incr_1: forall m, sup_In (nextblock m) (sup_incr (m.(support))).
Proof.
  intros. unfold nextblock. unfold sup_incr. apply sup_incr_in1.
Qed.

Lemma mem_incr_2: forall m b, sup_In b (m.(support)) -> sup_In b (sup_incr (m.(support))).
Proof.
  intros. unfold sup_incr. apply sup_incr_in2. auto.
Qed.

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (NMap.set _ (nextblock m)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (NMap.set _ (nextblock m)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (sup_incr (m.(support)))
         _ _ _,
   (nextblock m)).
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. elim H. apply mem_incr_1.
  apply nextblock_noaccess. red; intros; elim H.
  apply mem_incr_2. auto.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)). auto. apply contents_default.
Qed.

Lemma mem_incr_glob1: forall i m, sup_In (Global i) (sup_incr_glob i (m.(support))).
Proof.
  intros. simpl. auto.
Qed.

Lemma mem_incr_glob2: forall i m b, sup_In b (m.(support)) -> sup_In b (sup_incr_glob i (m.(support))).
Proof.
  intros. unfold sup_incr_glob. destruct b. auto. simpl in *. auto.
Qed.

Program Definition alloc_glob(i:ident) (m:mem) (lo hi:Z) :=
  ((mkmem (NMap.set _ (Global i)
                  (ZMap.init Undef)
                  m.(mem_contents))
        (NMap.set _ (Global i)
                  (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                  m.(mem_access))
        (sup_incr_glob i (m.(support)))
        _ _ _), (Global i)).
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b (Global i)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (Global i)).
  subst b. elim H. simpl. auto.
  apply nextblock_noaccess. red; intros; elim H.
  apply mem_incr_glob2. auto.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (Global i)). auto. apply contents_default.
Qed.

Program Definition alloc_frame (m:mem)(id:ident) :=
  ((mkmem (m.(mem_contents)) (m.(mem_access)) (sup_incr_frame (m.(support)) id) _ _ _), sup_npath (m.(support)) id).
Next Obligation.
  apply access_max.
Qed.
Next Obligation.
  apply nextblock_noaccess.
  intro. apply H.
  eapply sup_incr_frame_in in H0. eauto.
Qed.
Next Obligation.
  apply contents_default.
Qed.

Lemma is_active_dec : forall s, {is_active s} + {~ is_active s}.
Proof. intros. destruct s. destruct o; simpl; auto. Qed.

Program Definition return_frame (m:mem) : option mem :=
  if is_active_dec (stack(support m)) then
     Some (mkmem (m.(mem_contents))
                 (m.(mem_access))
                 (sup_return_frame' (support m))
                 (m.(access_max))
                 _
                 (m.(contents_default))
         )
     else None.
Next Obligation.
  apply nextblock_noaccess.
  eapply sup_return_refl' in H.
  intro. apply H0.
  eapply sup_return_frame_in in H.
  apply H. auto.
Qed.

Program Definition alloc_block (m: mem) (lo hi: Z) :=
  (mkmem (NMap.set _ (nextblock m)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (NMap.set _ (nextblock m)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (sup_incr (m.(support)))
         _ _ _,
   (nextblock m)).
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. elim H. apply mem_incr_1.
  apply nextblock_noaccess. red; intros; elim H.
  apply mem_incr_2. auto.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)). auto. apply contents_default.
Qed.

Program Definition push_stage (m:mem):=
  (mkmem m.(mem_contents)
         m.(mem_access)
         (sup_push_stage m.(support))
         m.(access_max)
         m.(nextblock_noaccess)
         m.(contents_default)
  ).

Program Definition pop_stage (m:mem) :=
  match astack (support m) with
    |hd::tl =>
       Some (mkmem m.(mem_contents)
         m.(mem_access)
         (mksup (stacks (support m))
                (setastack (astacks (support m)) (tl) (sid (support m)))
                (global (support m)) (sid (support m)) _ _)
         m.(access_max)
         m.(nextblock_noaccess)
         m.(contents_default)
  )
    |nil => None
  end.
Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  rewrite setastack_length. apply length_eq.
Qed.

Lemma setastack_setastack:forall n l a b,
    (n < length l)%nat ->
    setastack (setastack l a n) (nth n l b) n = l.
Proof.
  induction n; intros.
  - destruct l; auto.
  - destruct l; simpl; auto. rewrite IHn. auto. simpl in H. lia.
Qed.

Lemma pop_push_stage : forall m, pop_stage (push_stage m) = Some m.
Proof.
  intro. unfold push_stage. unfold sup_push_stage.
  unfold pop_stage. simpl. unfold astack. simpl.
  repeat rewrite setastack_astack.
  apply f_equal.
  destruct m. simpl. apply mkmem_ext; auto.
  destruct support0. apply mksup_ext; auto.
  simpl. apply setastack_setastack. lia.
  rewrite <- length_eq. apply sid_valid.
Qed.

Program Definition record_frame (m:mem)(fr:frame) :=
  if (zle (frame_size_a fr + (stack_size (astack (support m)))) max_stacksize) then
  match astack (support m) with
    |hd::tl =>
       Some (mkmem m.(mem_contents)
         m.(mem_access)
         (mksup (stacks (support m))
                (setastack (astacks (support m))((fr::hd)::tl) (sid (support m)))
                (global (support m)) (sid (support m)) _ _)
         m.(access_max)
         m.(nextblock_noaccess)
         m.(contents_default)
  )
    |nil => None
  end else None.

Next Obligation.
  apply sid_valid.
Qed.
Next Obligation.
  rewrite setastack_length. apply length_eq.
Qed.
(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (NMap.set _ b
                (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                m.(mem_access))
        m.(support) _ _ _.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.


Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (Z.to_nat n) ofs (m.(mem_contents)#b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. lia.
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. lia.
  apply IHvl.
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
  apply H. lia. apply IHn. intros. apply H. lia.
Qed.

Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (NMap.set _ b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(support)
                _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

Theorem support_storev: forall chunk m addr v m',
    storev chunk m addr v = Some m' -> support m = support m'.
Proof.
  intros.
  unfold storev in H.
  unfold store in H.
  destruct addr; try congruence.
  destruct (valid_access_dec m chunk b (Ptrofs.unsigned i) Writable).
  inv H.
  auto.
  congruence.
Qed.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable then
    Some (mkmem
             (NMap.set _ b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(support)
             _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (NMap.set _ b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(support) _ _ _)
  else None.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto.
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)
Theorem support_empty : support empty = sup_init.
Proof.
  reflexivity.
Qed.
Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. auto.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); lia.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_rettype:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = Z.to_nat n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite Z_to_nat_neg; auto.
  red; intros. extlia.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. lia.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by lia.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
  rewrite getN_concat. rewrite Z2Nat.id by lia.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
  destruct H4. apply r; lia. apply r0; lia.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
  rewrite Z2Nat.id in H by lia.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; lia.
  red; intros; apply r; lia.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite Nat2Z.inj_succ in H.
  replace ofs with (ofs+0) by lia.
  apply H; lia.
  apply IHn.
  intros.
  rewrite <- Z.add_assoc.
  apply H.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. lia. lia.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  lia. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. lia.
Qed.

Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_valid_access. eexact H2. intros [P Q]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = NMap.set _ b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem support_store:
  support m2 = support m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite support_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  setoid_rewrite NMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply Nat2Z.inj; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. lia.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  setoid_rewrite NMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. extlia.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. lia.
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. extlia.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. lia.
  right. apply IHvl. lia.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; extlia.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. lia.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  setoid_rewrite NMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by lia. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. lia. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. lia.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. lia. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  lia.
  unfold c'. simpl. rewrite setN_outside by lia. apply ZMap.gss.
Qed.

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (NMap.elt_eq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); lia.
  generalize (size_chunk_pos chunk); lia.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try extlia.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. lia.
  elim n. apply valid_access_compat with chunk2; auto. lia.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; lia.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
  econstructor; reflexivity.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable); inv H.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  f_equal. apply mkmem_ext; auto.
  elim n. constructor; auto.
  rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable).
  f_equal. apply mkmem_ext; auto.
  destruct v0.  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = NMap.set _ b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem support_storebytes:
  support m2 = support m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite support_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. setoid_rewrite NMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z.of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1)) (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  setoid_rewrite NMap.gss.  rewrite setN_concat. symmetry. apply NMap.set2.
  elim n.
  rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
  destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
  apply r. lia.
  eapply perm_storebytes_2; eauto. apply r0. lia.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros.
  destruct (range_perm_storebytes m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite Nat2Z.inj_add. lia.
  destruct (range_perm_storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite Nat2Z.inj_add. lia.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

Theorem storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P Q]. exact Q.
Qed.

Axiom loadv_val_storev:
  forall m ofs v b,
    loadv Mptr m (Vptr b ofs) = Some v ->
    v <> Vundef -> (align_chunk Mptr | Ptrofs.unsigned ofs) ->
    (forall o k p, perm m b o k p -> perm m b o k Writable) ->
    storev Mptr m (Vptr b ofs) v = Some m.

(** ** Properties related to [alloc_frame]. *)

Section ALLOC_FRAME.
Variable m1: mem.
Variable m2: mem.
Variable id: ident.
Variable path: path.
Hypothesis ALLOC_FRAME: alloc_frame m1 id = (m2,path).

Lemma support_alloc_frame :
    support m2 = sup_incr_frame (support m1) id.
Proof.
  intros. inv ALLOC_FRAME. reflexivity. Qed.

Lemma support_alloc_frame_1 :
  forall b, sup_In b (support m1) <-> sup_In b (support m2).
Proof.
  generalize support_alloc_frame. intro.
  rewrite H. intro.
  apply sup_incr_frame_in.
Qed.

Lemma stack_alloc_frame :
    (stack(support m2), path) = next_stree (stack (support m1)) id.
Proof.
  intros. inv ALLOC_FRAME. simpl.
  unfold sup_incr_frame. unfold sup_npath. unfold npath.
  destruct (next_stree (stack (support m1))).
  unfold stack. simpl. rewrite setstack_stack.
  reflexivity. apply sid_valid.
Qed.

Lemma astack_alloc_frame:
  astack (support m1) = astack (support m2).
Proof.
  rewrite support_alloc_frame. unfold sup_incr_frame.
  destr.
Qed.

Lemma sdepth_alloc_frame :
  sdepth m2 = S (sdepth m1).
Proof.
  unfold sdepth. generalize stack_alloc_frame.
  intro. eapply next_stree_cdepth; eauto.
Qed.

Lemma sid_alloc_frame:
  sid (support m1) = sid (support m2).
Proof.
  rewrite support_alloc_frame. unfold sup_incr_frame.
  destr.
Qed.

Lemma path_alloc_frame:
    path = sup_npath (support m1) id.
Proof.
  intros. inv ALLOC_FRAME. reflexivity. Qed.

Lemma cpath_alloc_frame:
   path = cpath (stack (support m2)).
Proof.
  exploit next_stree_cpath; eauto.
  rewrite stack_alloc_frame. eauto.
Qed.

Theorem valid_block_alloc_frame_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block. rewrite support_alloc_frame.
  intro. eapply sup_incr_frame_in.
Qed.

Theorem valid_block_alloc_frame_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  unfold valid_block. rewrite support_alloc_frame.
  intro. eapply sup_incr_frame_in.
Qed.

Local Hint Resolve valid_block_alloc_frame_1 valid_block_alloc_frame_2: mem.

Theorem perm_alloc_frame:
  forall b ofs k p,
  perm m1 b ofs k p <->
  perm m2 b ofs k p.
Proof.
  inv ALLOC_FRAME. simpl. unfold perm. simpl.
  reflexivity.
Qed.

Theorem valid_access_alloc_frame:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p <->
  valid_access m2 chunk b ofs p.
Proof.
  inv ALLOC_FRAME. unfold valid_access. unfold range_perm.
  unfold perm. simpl. reflexivity.
Qed.

Theorem load_alloc_frame:
  forall chunk b ofs,
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  inv ALLOC_FRAME. simpl. reflexivity.
  apply valid_access_alloc_frame. auto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_alloc_frame; eauto.
Qed.

Theorem load_alloc_frame_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros.
  unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H).
  inv ALLOC_FRAME. reflexivity.
  apply valid_access_alloc_frame. eauto with mem.
Qed.

Theorem loadbytes_alloc_frame:
  forall b ofs n,
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  inv ALLOC_FRAME. reflexivity.
  red; intros. eapply perm_alloc_frame; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_alloc_frame; eauto.
Qed.

End ALLOC_FRAME.

(** ** Properties related to [return_frame]. *)

Lemma active_return_frame : forall m,
    is_active(stack (support m)) -> {m'|return_frame m = Some m'}.
Proof.
  intros; unfold return_frame.
  destruct (is_active_dec (stack(support m))).
  econstructor; eauto.
  congruence.
Qed.

Section RETURN_FRAME.

Variable m1: mem.
Variable m2: mem.
Hypothesis RETURN_FRAME: return_frame m1 = Some m2.

Lemma return_frame_active : forall m m',
    return_frame m = Some m' ->
    is_active (stack (support m)).
Proof.
  intros. unfold return_frame in H.
  destr_in H.
Qed.

Lemma support_return_frame :
    sup_return_frame (support m1) = Some (support m2).
Proof.
  unfold return_frame in RETURN_FRAME.
  destr_in RETURN_FRAME. inv RETURN_FRAME.
  simpl.
  apply sup_return_refl'. auto.
Qed.

Lemma support_return_frame_1:
  forall b, (sup_In b (support m1)) <-> (sup_In b (support m2)).
Proof.
  intros. generalize support_return_frame. intro.
  apply sup_return_frame_in. eauto.
Qed.

Lemma stack_return_frame:
  exists path,
  return_stree (stack(support m1)) = Some (stack (support m2),path).
Proof.
  intros.
  generalize support_return_frame.
  intro. unfold sup_return_frame in H.
  destr_in H. destruct p. inv H.
  unfold stack. simpl. rewrite setstack_stack.
  eauto. apply sid_valid.
Qed.

Lemma astack_return_frame:
  astack (support m1) = astack (support m2).
Proof.
  generalize support_return_frame.
  intro. unfold sup_return_frame in H.
  repeat destr_in H.
  unfold astack. simpl. congruence.
Qed.

Lemma sid_return_frame:
  sid (support m1) = sid (support m2).
Proof.
  generalize support_return_frame.
  intro. unfold sup_return_frame in H.
  repeat destr_in H.
  unfold astack. simpl. congruence.
Qed.

Lemma sdepth_return_frame :
  S (sdepth m2) = sdepth m1.
Proof.
  generalize stack_return_frame. intros [pa H].
  eapply return_stree_cdepth; eauto.
Qed.

Lemma sup_include_return_frame :
  sup_include (support m1) (support m2).
Proof.
  unfold sup_include. apply support_return_frame_1.
Qed.

Theorem valid_block_return_frame_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block. apply support_return_frame_1.
Qed.

Theorem valid_block_return_frame_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
    unfold valid_block. apply support_return_frame_1.
Qed.

Local Hint Resolve valid_block_return_frame_1 valid_block_return_frame_2: mem.

Theorem perm_return_frame:
  forall b ofs k p,
  perm m1 b ofs k p <->
  perm m2 b ofs k p.
Proof.
  inv RETURN_FRAME.
  unfold return_frame in H0. destr_in H0.
  inv H0. intros.
  reflexivity.
Qed.

Theorem valid_access_return_frame:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p <->
  valid_access m2 chunk b ofs p.
Proof.
  split.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_return_frame; eauto.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_return_frame; eauto.
Qed.

Theorem load_return_frame:
  forall chunk b ofs,
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  inv RETURN_FRAME.
  unfold return_frame in H0. destr_in H0.
  inv H0. intros.
  reflexivity.
Qed.

Theorem loadbytes_return_frame:
  forall b ofs n,
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  inv RETURN_FRAME.
  unfold return_frame in H0. destr_in H0.
  inv H0. intros.
  reflexivity.
Qed.

End RETURN_FRAME.

Local Hint Resolve valid_block_return_frame_1 valid_block_return_frame_2
             perm_return_frame
             valid_access_return_frame: mem.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = fresh_block (sup_incr(support m1)).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem support_alloc:
  support m2 = sup_incr(support m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Lemma sup_include_alloc :
  sup_include (support m1) (support m2).
Proof.
  rewrite support_alloc. intro. apply mem_incr_2.
Qed.

Theorem sdepth_alloc:
  sdepth m2 = sdepth m1.
Proof.
  generalize support_alloc. unfold sup_incr.
  destr. intro. unfold sdepth. rewrite H. simpl.
  unfold stack. simpl.
  rewrite setstack_stack.
  destruct p. destruct p.
  eapply next_block_stree_cdepth; eauto.
  apply sid_valid.
Qed.

Theorem astack_alloc:
  astack (support m2) = astack (support m1).
Proof.
  rewrite support_alloc. unfold sup_incr.
  destr.
Qed.

Lemma sid_alloc:
  sid (support m2) = sid (support m1).
Proof.
  rewrite support_alloc. unfold sup_incr. destr.
Qed.

Theorem stack_alloc :
  stack (support m2) = snd (next_block_stree (stack (support m1))).
Proof.
  generalize support_alloc. unfold sup_incr.
  destr. simpl. intro. rewrite H.
  unfold stack. simpl.
  rewrite setstack_stack. auto.
  apply sid_valid.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem alloc_result_stack:
  is_stack b.
Proof.
  rewrite alloc_result.
  generalize (nextblock_stack m1).
  intros (f & p & p' & H). rewrite H. auto.
  simpl. auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_alloc.
  apply mem_incr_2. auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply freshness.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite support_alloc. apply mem_incr_1.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite support_alloc in H. rewrite alloc_result.
  apply sup_incr_in. auto.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite NMap.gsspec. destruct (NMap.elt_eq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply freshness.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold NMap.get. rewrite NMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. lia. lia.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite NMap.gsspec.  destruct (NMap.elt_eq b' (nextblock m1)); intros.
  assert (zle lo ofs && zlt ofs hi = true).
    destruct(zle lo ofs && zlt ofs hi). reflexivity. contradiction.
  - destruct(eq_block b' (nextblock m1)).
    + split. destruct (zle lo ofs); try auto. try contradiction.
    destruct (zlt ofs hi). try auto. simpl in H.
    destruct (zle lo ofs); simpl in H; contradiction.
    + congruence.
  - destruct (eq_block b' (nextblock m1)).
    + congruence.
    + auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. lia.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  setoid_rewrite NMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  setoid_rewrite NMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. setoid_rewrite NMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H. destruct H; eauto.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Section ALLOCF_ALLOC.
Local Set Elimination Schemes.

Inductive alloc_vars_left : mem -> list block -> mem -> Prop :=
  |avl_nil : forall m, alloc_vars_left m nil m
  |avl_cons : forall m m1 m2 blocks b sz,
      alloc_vars_left m blocks m1 ->
      Mem.alloc m1 0 sz = (m2,b) ->
      alloc_vars_left m (blocks++(b::nil)) m2.

Fixpoint well_blocks (sid:nat)(id:ident) (p:path) (len:nat) : list block :=
  match len with
    |O => nil
    |S n => (well_blocks sid id p n) ++ ((Stack sid (Some id) p (Pos.of_nat len))::nil)
  end.

Definition well_nth_error (sid:nat)(l:list block) (id:ident) (p:path) : Prop :=
  let len := length l in
  forall n0, (n0 < len)%nat -> nth_error l n0 = Some (Stack sid (Some id) p (Pos.of_succ_nat n0)).

Lemma well_blocks_len : forall id p sid n,
  length (well_blocks sid id p n) = n.
Proof.
  induction n. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma well_blocks_nth_error : forall id p sid n,
    well_nth_error sid (well_blocks sid id p n) id p.
Proof.
  induction n; intros.
  - unfold well_nth_error. intros. inv H.
  - unfold well_nth_error in *.
    intros. simpl in H. rewrite app_length in H. simpl in H.
    rewrite well_blocks_len in H.
    destruct (nat_eq n0 n).
    + subst. simpl. rewrite nth_error_app2. rewrite well_blocks_len.
      rewrite Nat.sub_diag. simpl. destruct n; auto.
      rewrite Pos.succ_of_nat. auto. auto.
      rewrite well_blocks_len. lia.
    + simpl. rewrite nth_error_app1. eapply IHn.
      rewrite well_blocks_len. lia.
      rewrite well_blocks_len. lia.
Qed.

Lemma alloc_frame_alloc : forall m m1 m2 id path lo hi sp,
    alloc_frame m id = (m1,path) ->
    alloc m1 lo hi = (m2,sp) ->
    sp = Stack (sid (support m1)) (Some id) path 1.
Proof.
  intros. unfold alloc in H0. inv H0.
  inv H. unfold nextblock. simpl. unfold sup_incr_frame.
  destruct (next_stree (stack (support m))id) eqn:?. unfold fresh_block. simpl.
  unfold stack. simpl. rewrite setstack_stack.
  destruct (next_block_stree s) eqn:?. destruct p0. destruct p0.
  unfold sup_npath. unfold npath. rewrite Heqp.
  exploit next_stree_next_block_stree; eauto. intros (A & B & C).
  congruence. apply sid_valid.
Qed.

Lemma alloc_frame_nextblock : forall m m1 id path,
    alloc_frame m id = (m1,path) ->
    nextblock m1 = Stack (sid (support m1))(Some id) path 1.
Proof.
  intros. caseEq (alloc m1 0 0). intros.
  apply alloc_result in H0 as H1. subst.
  eapply alloc_frame_alloc; eauto.
Qed.

Lemma alloc_alloc : forall m1 m2 m3 lo1 hi1 lo2 hi2 b1 b2 fid path pos sid,
    alloc m1 lo1 hi1 = (m2,b1) ->
    alloc m2 lo2 hi2 = (m3,b2) ->
    b1 = Stack sid fid path pos ->
    b2 = Stack sid fid path (Pos.succ pos).
Proof.
  intros. inv H. inv H0. unfold nextblock in *.
  simpl in *. unfold sup_incr.
  unfold fresh_block in *.
  destruct (next_block_stree (stack (support m1))) eqn:?.
  unfold stack. simpl. rewrite setstack_stack.
  destruct p. destruct p.
  simpl.
  destruct (next_block_stree s) eqn:?.
  destruct p1. destruct p1.
  inv H4.
  exploit next_block_stree_next_block. apply Heqp. eauto.
  intros [A [B C]]. subst. auto. apply sid_valid.
Qed.

Lemma alloc_frame_alloc_vars :
  forall m m1 m2 id path blocks,
    alloc_frame m id = (m1,path) ->
    alloc_vars_left m1 blocks m2 ->
    blocks = well_blocks (sid (support m1))id path (length blocks).
Proof.
  intros. induction H0.
  - reflexivity.
  - exploit IHalloc_vars_left; eauto. intro.
    rewrite app_length. simpl.
    assert (Datatypes.length blocks +1 = S (Datatypes.length blocks))%nat.
    lia. rewrite H3. simpl.
    rewrite <- H2.
    inv H0.
    + simpl. exploit alloc_frame_alloc; eauto.
      intro. subst. auto.
    + simpl. rewrite app_length.
      rewrite Nat.add_1_r.
      generalize (well_blocks_nth_error id path (sid (support m0))(Datatypes.length (blocks0 ++ b0 :: nil))).
      intros. rewrite <- H2 in H0.
      unfold well_nth_error in H0.
      generalize (H0 (Datatypes.length (blocks0))).
      intros. exploit H6. rewrite app_length. simpl. lia. intro.
      rewrite nth_error_app2 in H7. rewrite Nat.sub_diag in H7.
      simpl in H7. inv H7. 2:lia.
      exploit alloc_alloc; eauto.
      intro. subst. rewrite Pos.of_nat_succ. reflexivity.
Qed.
End ALLOCF_ALLOC.

(** ** Properties related to [alloc_glob]. *)
Section ALLOCGLOB.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable id: ident.
Variable b: block.
Hypothesis ALLOC: alloc_glob id m1 lo hi = (m2, b).

Theorem nextblock_alloc_glob:
  nextblock m2 = nextblock m1.
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem support_alloc_glob:
  support m2 = sup_incr_glob id(support m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_glob_result :
  b = Global id.
Proof. inv ALLOC. auto. Qed.

Theorem perm_alloc_glob_1 : forall ofs k p b,
    b <> Global id ->
    perm m1 b ofs k p <-> perm m2 b ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold NMap.get. rewrite NMap.gso. reflexivity. auto.
Qed.

Theorem perm_alloc_glob_2:
  forall ofs k p, lo <= ofs < hi <-> perm m2 b ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H0; simpl.
  subst b. unfold NMap.get. rewrite NMap.gss. unfold proj_sumbool.
  split; intro.
  rewrite zle_true. rewrite zlt_true. simpl. auto with mem. lia. lia.
  destruct (zle lo ofs); destruct (zlt ofs hi); simpl in H; try (inv H). lia. lia. lia.
Qed.

Local Hint Resolve perm_alloc_glob_1 perm_alloc_glob_2 : mem.

Theorem valid_access_alloc_glob:
  forall chunk b ofs p,
  b <> Global id ->
  valid_access m2 chunk b ofs p <-> valid_access m1 chunk b ofs p.
Proof.
  intros. inv ALLOC. unfold valid_access. simpl.
  unfold range_perm. unfold perm. simpl.
  unfold NMap.get. rewrite NMap.gso. reflexivity. auto.
Qed.

Theorem load_alloc_glob_unchanged:
  forall chunk b ofs,
  b <> Global id ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  eapply valid_access_alloc_glob in H as H1; eauto.
  repeat destr. inv ALLOC. simpl. unfold NMap.get. rewrite NMap.gso.
  reflexivity. auto.
  apply H1 in v. congruence.
  apply H1 in v. congruence.
Qed.

Theorem load_alloc_glob_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  setoid_rewrite NMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem loadbytes_alloc_glob_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. setoid_rewrite NMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H. destruct H; eauto.
Qed.

Theorem loadbytes_alloc_glob_unchanged:
  forall b' ofs n,
  b' <> Global id ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  inv ALLOC. simpl. unfold NMap.get. rewrite NMap.gso.
  reflexivity. auto. red; intros. eapply perm_alloc_glob_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_glob_1; eauto.
Qed.

End ALLOCGLOB.

Lemma astack_push_stage : forall m,
  astack (support (push_stage m)) = nil :: astack (support m).
Proof.
  intros. unfold push_stage. simpl.
  unfold sup_push_stage. unfold astack. simpl.
  rewrite setastack_astack. auto. rewrite <- length_eq.
  apply sid_valid.
Qed.

Lemma stack_push_stage : forall m,
  stack (support (push_stage m)) = stack (support m).
Proof. reflexivity. Qed.

Section PUSH_STAGE.

Variable m1: mem.
Variable m2: mem.
Hypothesis PUSH_STAGE: push_stage m1 = m2.

Lemma support_push_stage :
    support m2 = sup_push_stage (support m1).
Proof.
  intros. unfold push_stage in PUSH_STAGE. rewrite <- PUSH_STAGE.
  reflexivity.
Qed.

Lemma support_push_stage_1 :
  forall b, sup_In b (support m1) <-> sup_In b (support m2).
Proof.
  rewrite support_push_stage. unfold sup_push_stage.
  destruct b; reflexivity.
Qed.

Theorem sdepth_push_stage:
  sdepth m2 = sdepth m1.
Proof.
  unfold sdepth. rewrite support_push_stage.
  reflexivity.
Qed.

Theorem nextblock_push_stage:
  nextblock m2 = nextblock m1.
Proof.
  unfold nextblock. rewrite support_push_stage. unfold fresh_block.
  reflexivity.
Qed.

Theorem valid_block_push_stage_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block. rewrite support_push_stage. auto.
Qed.

Theorem valid_block_push_stage_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  unfold valid_block. rewrite support_push_stage. auto.
Qed.

Local Hint Resolve valid_block_push_stage_1 valid_block_push_stage_2: mem.

Theorem perm_push_stage:
  forall b ofs k p,
  perm m1 b ofs k p <->
  perm m2 b ofs k p.
Proof.
  inv PUSH_STAGE. unfold perm. reflexivity.
Qed.

Theorem valid_access_push_stage:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p <->
  valid_access m2 chunk b ofs p.
Proof.
  inv PUSH_STAGE. reflexivity.
Qed.

Theorem load_push_stage:
  forall chunk b ofs,
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true. rewrite <- PUSH_STAGE. reflexivity.
  eapply valid_access_push_stage; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_push_stage; eauto.
Qed.

Theorem load_push_stage_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite <- PUSH_STAGE. reflexivity.
  apply valid_access_push_stage. eauto with mem.
Qed.

Theorem loadbytes_push_stage:
  forall b ofs n,
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite <- PUSH_STAGE. reflexivity.
  red; intros. eapply perm_push_stage; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_push_stage; eauto.
Qed.

End PUSH_STAGE.

Lemma nonempty_pop_stage : forall m1,
   astack (support m1) <> nil -> {m2:mem|pop_stage m1 = Some m2}.
Proof.
  intros; unfold pop_stage. destruct (astack (support m1)). congruence.
  econstructor; eauto.
Qed.

Section POP_STAGE.

Variable m1: mem.
Variable m2: mem.
Hypothesis POP_STAGE: pop_stage m1 = Some m2.

Lemma pop_stage_nonempty :
   astack (support m1) <> nil.
Proof.
  intros. unfold pop_stage in POP_STAGE. destruct (astack(support m1)); auto.
  discriminate. congruence.
Qed.

Lemma support_pop_stage :
    sup_pop_stage (support m1) = Some (support m2).
Proof.
  intros. unfold pop_stage in POP_STAGE. destruct (astack(support m1)) eqn:H0; auto.
  discriminate. inv POP_STAGE.
  unfold sup_pop_stage. simpl. rewrite H0.
  apply f_equal. apply mksup_ext; auto.
Qed.

Lemma support_pop_stage_1 :
  forall b, sup_In b (support m1) <-> sup_In b (support m2).
Proof.
  generalize support_pop_stage. intro. unfold sup_pop_stage in H.
  destr_in H. inv H.  destruct b; reflexivity.
Qed.

Lemma astack_pop_stage:
      exists hd,
        astack(support m1) = hd :: (astack(support m2)).
Proof.
  intros.
  unfold pop_stage in POP_STAGE.
  destruct (astack (support m1)).
  discriminate.
  inv POP_STAGE. simpl. unfold astack. simpl.
  rewrite setastack_astack.
  exists s. auto. rewrite <- length_eq. apply sid_valid.
Qed.

Lemma stack_pop_stage :
  stack (support m1) = stack (support m2).
Proof.
  unfold pop_stage in POP_STAGE. destruct (astack (support m1)).
  discriminate. inv POP_STAGE. auto.
Qed.

Lemma sdepth_pop_stage :
  sdepth m2 = sdepth m1.
Proof.
  unfold sdepth. rewrite stack_pop_stage. reflexivity.
Qed.

Lemma global_pop_stage :
  global (support m1) = global (support m2).
Proof.
  unfold pop_stage in POP_STAGE. destruct (astack (support m1)).
  discriminate. inv POP_STAGE. auto.
Qed.

Lemma sid_pop_stage :
  sid (support m1) = sid (support m2).
Proof.
  unfold pop_stage in POP_STAGE. destruct (astack (support m1)).
  discriminate. inv POP_STAGE. auto.
Qed.

Lemma sup_include_pop_stage :
  sup_include (support m1) (support m2).
Proof.
  unfold sup_include, sup_In. rewrite stack_pop_stage.
  rewrite global_pop_stage. rewrite sid_pop_stage. auto.
Qed.

Theorem nextblock_pop_stage:
  nextblock m2 = nextblock m1.
Proof.
  unfold nextblock. unfold fresh_block.
  rewrite stack_pop_stage. rewrite sid_pop_stage. auto.
Qed.

Theorem valid_block_pop_stage_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block, sup_In. rewrite stack_pop_stage.
  rewrite global_pop_stage. rewrite sid_pop_stage. auto.
Qed.

Theorem valid_block_pop_stage_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  unfold valid_block, sup_In. rewrite stack_pop_stage.
  rewrite global_pop_stage. rewrite sid_pop_stage. auto.
Qed.

Local Hint Resolve valid_block_pop_stage_1 valid_block_pop_stage_2: mem.

Theorem perm_pop_stage:
  forall b ofs k p,
  perm m1 b ofs k p <->
  perm m2 b ofs k p.
Proof.
  intros. unfold pop_stage in POP_STAGE. destruct (astack(support m1)); auto.
  discriminate. inv POP_STAGE. auto. reflexivity.
Qed.


Theorem valid_access_pop_stage:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p <->
  valid_access m2 chunk b ofs p.
Proof.
  split;(
  intros; inv H; constructor; auto with mem;
  red; intros; eapply perm_pop_stage; eauto ).
Qed.

Theorem load_pop_stage:
  forall chunk b ofs,
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold pop_stage in POP_STAGE. destruct (astack(support m1)); auto. discriminate. inv POP_STAGE. simpl. reflexivity.
Qed.

Theorem loadbytes_pop_stage:
  forall b ofs n,
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold pop_stage in POP_STAGE. destruct (astack(support m1)); auto. discriminate. inv POP_STAGE. simpl. reflexivity.
Qed.

End POP_STAGE.

Local Hint Resolve valid_block_pop_stage_1 valid_block_pop_stage_2
             perm_pop_stage
             valid_access_pop_stage: mem.

Lemma request_record_frame : forall m1 fr,
   astack (support m1) <> nil  ->
    frame_size_a fr  + stack_size (astack(support m1)) <= max_stacksize
   -> {m2:mem| record_frame m1 fr = Some m2}.
Proof.
  intros; unfold record_frame. rewrite zle_true.
  destruct (astack (support m1)); simpl.
  congruence. simpl in *. eauto. lia.
Qed.

Section RECORD_FRAME.

Variable m1: mem.
Variable m2: mem.
Variable fr: frame.

Hypothesis RECORD_FRAME: record_frame m1 fr = Some m2.

Lemma record_frame_size :
    (stack_size (astack(support m2))) <= max_stacksize.
Proof.
  intros. unfold record_frame in RECORD_FRAME. repeat destr_in RECORD_FRAME.
  unfold astack. simpl. rewrite setastack_astack. simpl in *. lia.
  rewrite <- length_eq. apply sid_valid.
Qed.

Lemma record_frame_size1:
  (frame_size_a fr + stack_size (astack (support m1))) <= max_stacksize.
Proof.
  intros. unfold record_frame in RECORD_FRAME.   repeat destr_in RECORD_FRAME.
Qed.

Lemma record_frame_nonempty :
   astack (support m1) <> nil.
Proof.
  intros. unfold record_frame in RECORD_FRAME. repeat destr_in RECORD_FRAME.
Qed.

Lemma support_record_frame :
    sup_record_frame fr (support m1) = Some (support m2).
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. unfold sup_record_frame. rewrite Heqs.
  apply f_equal. apply mksup_ext; auto.
Qed.

Lemma support_record_frame_1:
  forall b, sup_In b (support m1) <-> sup_In b (support m2).
Proof.
  intros. generalize support_record_frame. unfold sup_record_frame.
  destr. intro. inv H. destruct b; reflexivity.
Qed.

Lemma astack_record_frame : exists hd tl,
  astack (support m1) = hd::tl /\
  astack (support m2) = (fr::hd)::tl.
Proof.
  intros. generalize support_record_frame. unfold sup_record_frame. intro.
  generalize record_frame_nonempty.
  destruct (astack (support m1)). intro.
  discriminate. inv RECORD_FRAME. intro. inv H.
  exists s. exists s0. auto. unfold astack. simpl. rewrite setastack_astack.
  auto. rewrite <- length_eq. apply sid_valid.
Qed.

Lemma stack_record_frame :
  stack (support m1) = stack (support m2).
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. reflexivity.
Qed.

Lemma sdepth_record_frame :
  sdepth m2 = sdepth m1.
Proof.
  unfold sdepth. rewrite stack_record_frame. reflexivity.
Qed.

Lemma global_record_frame :
  global (support m1) = global (support m2).
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. reflexivity.
Qed.

Lemma sid_record_frame :
  sid (support m1) = sid (support m2).
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. reflexivity.
Qed.

Lemma sup_include_record_frame :
  sup_include (support m1) (support m2).
Proof.
  unfold sup_include. unfold sup_In. rewrite sid_record_frame.
  rewrite stack_record_frame. rewrite global_record_frame. auto.
Qed.

Theorem nextblock_record_frame:
  nextblock m2 = nextblock m1.
Proof.
  unfold nextblock. unfold fresh_block.  rewrite sid_record_frame.
  rewrite stack_record_frame. auto.
Qed.

Theorem valid_block_record_frame_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  unfold valid_block. unfold sup_In.  rewrite sid_record_frame.
  rewrite stack_record_frame. rewrite global_record_frame. auto.
Qed.

Theorem valid_block_record_frame_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  unfold valid_block. unfold sup_In.  rewrite sid_record_frame.
  rewrite stack_record_frame. rewrite global_record_frame. auto.
Qed.

Local Hint Resolve valid_block_record_frame_1 valid_block_record_frame_2: mem.

Theorem perm_record_frame:
  forall b ofs k p,
  perm m1 b ofs k p <->
  perm m2 b ofs k p.
Proof.
  intros. unfold record_frame in RECORD_FRAME. repeat destr_in RECORD_FRAME.
  unfold perm. reflexivity.
Qed.

Theorem valid_access_record_frame:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p <->
  valid_access m2 chunk b ofs p.
Proof.
  split.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_record_frame; eauto.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_record_frame; eauto.
Qed.

Theorem load_record_frame:
  forall chunk b ofs,
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. auto.
Qed.

Theorem loadbytes_record_frame:
  forall b ofs n,
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold record_frame in RECORD_FRAME.
  repeat destr_in RECORD_FRAME. auto.
Qed.

End RECORD_FRAME.

Local Hint Resolve valid_block_record_frame_1 valid_block_record_frame_2
             perm_record_frame
             valid_access_record_frame: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
  congruence. congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem support_free:
  support m2 = support m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Lemma sdepth_free:
  sdepth m2 = sdepth m1.
Proof.
  unfold sdepth. rewrite support_free. auto.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold NMap.get. rewrite NMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. lia.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem support_drop:
  support m' = support m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite support_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite support_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. unfold NMap.get. rewrite NMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  lia. lia.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. unfold NMap.get. rewrite NMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  lia. lia.
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition lia.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite NMap.gsspec. destruct (NMap.elt_eq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
Qed.

Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. apply H0. lia.
Qed.

Lemma valid_access_inj:
  forall f m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as [A B]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by lia.
  eapply range_perm_inj; eauto.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z.of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite Nat2Z.inj_succ in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by lia.
  apply IHn. red; intros; apply H1; lia.
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. apply getN_inj; auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
  eapply range_perm_inj; eauto with mem.
  apply getN_inj; auto.
  destruct (zle 0 len). rewrite Z2Nat.id by lia. auto.
  rewrite Z_to_nat_neg by lia. simpl. red; intros; extlia.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by lia.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma neq_true : forall (A:Type)(b:block)(a1 a2:A),
    (if eq_block b b then a1 else a2) =a1.
Proof.
  intros. destruct (eq_block b b).
  auto. congruence.
Qed.

Lemma neq_false : forall (A:Type) (b1 b2:block) (a1 a2:A),
    (b1<>b2)->(if eq_block b1 b2 then a1 else a2) = a2.
Proof.
  intros. destruct (eq_block b1 b2).
  congruence. auto.
Qed.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite neq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (NMap.elt_eq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  setoid_rewrite NMap.gso. eapply mi_memval; eauto with mem.
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite NMap.gsspec. destruct (NMap.elt_eq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
       with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). lia.
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE].
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite ! NMap.gsspec. destruct (NMap.elt_eq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite neq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (NMap.elt_eq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto 6 with mem.
  destruct H9. congruence. lia.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  setoid_rewrite NMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 b ofs bytes2 m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  rewrite NMap.gsspec. destruct (NMap.elt_eq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes2)) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  simpl. rewrite ! NMap.gsspec.
  destruct (NMap.elt_eq b0 b1); destruct (NMap.elt_eq b3 b2); subst; eapply mi_memval0; eauto.
Qed.

(*
Lemma alloc_frame_left_inj:
  forall f m1 m2 m1' id path,
  mem_inj f m1 m2 ->
  alloc_frame m1 id = (m1',path) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor; inv H0; eauto.
Qed.

Lemma alloc_frame_right_inj:
  forall f m1 m2 m2' id path,
  mem_inj f m1 m2 ->
  alloc_frame m2 id= (m2',path) ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor; inv H0; eauto.
Qed.

Lemma return_frame_left_inj:
  forall f m1 m2 m1',
  mem_inj f m1 m2 ->
  return_frame m1 = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. unfold return_frame in H0. destr_in H0.
  inversion H. constructor; inv H0; eauto.
Qed.

Lemma return_frame_right_inj:
  forall f m1 m2 m2',
  mem_inj f m1 m2 ->
  return_frame m2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. unfold return_frame in H0. destr_in H0.
  inversion H. constructor; inv H0; eauto.
Qed.
*)
(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. setoid_rewrite NMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite NMap.gsspec. (*unfold eq_block in H4.*) destruct (NMap.elt_eq b0 b1).
  rewrite ZMap.gi. constructor. apply mi_memval0. auto. eapply perm_alloc_4 in H0. apply H0. auto. auto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). rewrite ZMap.gi. constructor.
  apply mi_memval. auto. auto. eapply perm_alloc_4 in H0. eauto. auto. auto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
Qed.

Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  lia.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
Qed.

Lemma push_stage_left_inj:
  forall f m1 m2 m1',
  mem_inj f m1 m2 ->
  push_stage m1 = m1' ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. inv H0. constructor; auto.
Qed.

Lemma push_stage_right_inj:
  forall f m1 m2 m2',
  mem_inj f m1 m2 ->
  push_stage m2 = m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. inv H0. constructor; auto.
Qed.

Lemma pop_stage_left_inj:
  forall f m1 m2 m1',
  mem_inj f m1 m2 ->
  pop_stage m1 = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. unfold pop_stage in H0. destr_in H0.
  inversion H. inv H0. constructor; auto.
Qed.

Lemma pop_stage_right_inj:
  forall f m1 m2 m2',
  mem_inj f m1 m2 ->
  pop_stage m2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. unfold pop_stage in H0. destr_in H0.
  inversion H. inv H0. constructor; auto.
Qed.

Lemma record_frame_left_inj:
  forall f fr m1 m2 m1',
  mem_inj f m1 m2 ->
  record_frame m1 fr = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. unfold record_frame in H0. repeat destr_in H0.
  inversion H. constructor; auto.
Qed.

Lemma record_frame_right_inj:
  forall f fr m1 m2 m2',
  mem_inj f m1 m2 ->
  record_frame m2 fr = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. unfold record_frame in H0. repeat destr_in H0.
  inversion H. constructor; auto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros.
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. lia.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. lia.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. lia. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_outside_inj: forall f m1 m2 b lo hi p m2',
  mem_inj f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. lia.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_sup: support m1 = support m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia.
  apply memval_lessdef_refl.
  tauto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by lia. eapply loadbytes_inj; eauto.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (support_store _ _ _ _ _ _ H0).
  rewrite (support_store _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (support_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_store_2.
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.

Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (support_storebytes _ _ _ _ _ H0).
  rewrite (support_storebytes _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (support_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_storebytes_2.
Qed.

Theorem alloc_frame_extends:
  forall m1 m2 m1' id path,
    extends m1 m2 ->
    alloc_frame m1 id = (m1',path) ->
    exists m2',
      alloc_frame m2 id = (m2',path)
      /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc_frame m2 id). intros m2' p H1.
  exists m2'. split.
  apply path_alloc_frame in H0.
  apply path_alloc_frame in H1.
  subst. congruence.
  inv H0. inv H1.
  constructor; eauto.
  - simpl. congruence.
  - inv mext_inj0. constructor;auto.
Qed.

Theorem return_frame_parallel_extends:
  forall m1 m2 m1',
    extends m1 m2 ->
    return_frame m1 = Some m1' ->
    exists m2',
      return_frame m2 = Some m2'
      /\extends m1' m2'.
Proof.
  intros. inv H.
  apply return_frame_active in H0 as H1.
  rewrite mext_sup0 in H1.
  apply active_return_frame in H1. destruct H1 as (m2' & H1).
  exists m2'. split. auto.
  unfold return_frame in *. destr_in H0. destr_in H1.
  inv H0. inv H1.
  constructor; simpl.
  - congruence.
  - inv mext_inj0. constructor; eauto.
  - eauto.
Qed.

Theorem push_stage_extends:
  forall m1 m2,
  extends m1 m2 ->
  extends (push_stage m1) (push_stage m2).
Proof.
  intros. inv H.
  constructor; unfold push_stage;simpl.
  - rewrite mext_sup0. reflexivity.
  - inv mext_inj0. constructor; auto.
  - auto.
Qed.

Theorem pop_stage_extends:
  forall m1 m1' m2,
  extends m1 m2 ->
  pop_stage m1 = Some m1' ->
  exists m2', pop_stage m2 = Some m2' /\
         extends m1' m2'.
Proof.
  intros. inv H.
  apply pop_stage_nonempty in H0 as H1.
  rewrite mext_sup0 in H1.
  apply nonempty_pop_stage in H1.
  destruct H1 as [m2' POP]. exists m2'.
  split. auto.
  constructor; eauto.
  - apply support_pop_stage in H0.
    apply support_pop_stage in POP.
    congruence.
  - eapply pop_stage_right_inj with (m1 := m1'); eauto.
    eapply pop_stage_left_inj; eauto.
  - intros. exploit mext_perm_inv0.
    eapply perm_pop_stage in POP; eauto. apply POP in H. apply H.
    intros [A|A].
    eapply perm_pop_stage in H0; eauto. left. apply H0. auto.
    right; intuition eauto.
    apply A. eapply perm_pop_stage in H0; eauto. apply H0. auto.
Qed.

Theorem record_frame_safe_extends:
  forall m1 m1' m2 m2' fr,
  extends m1 m2 ->
  record_frame m1 fr = Some m1' ->
  record_frame m2 fr = Some m2' ->
  extends m1' m2'.
Proof.
  intros. inv H.
  constructor.
  - apply support_record_frame in H0.
    apply support_record_frame in H1.
    congruence.
  - eapply record_frame_right_inj with (m1 := m1'); eauto.
    eapply record_frame_left_inj; eauto.
  - intros. exploit mext_perm_inv0.
    eapply perm_record_frame in H1; eauto. apply H1 in H. apply H.
    intros [A|A].
    eapply perm_record_frame in H0; eauto. left. apply H0. auto.
    right; intuition eauto.
    apply A. eapply perm_record_frame in H0; eauto. apply H0. auto.
Qed.

Theorem record_frame_extends:
  forall m1 m1' m2 fr,
  extends m1 m2 ->
  record_frame m1 fr= Some m1' ->
  exists m2', record_frame m2 fr = Some m2' /\
    extends m1' m2'.
Proof.
  intros. inv H.
  apply record_frame_size1 in H0 as SIZE.
  assert ({m2':mem|record_frame m2 fr = Some m2'}).
  apply request_record_frame. auto.
  apply record_frame_nonempty in H0. congruence. rewrite <- mext_sup0. lia.
  destruct X as [m2' RECORD]. exists m2'. split. auto.
  constructor.
  - apply support_record_frame in H0.
    apply support_record_frame in RECORD.
    congruence.
  - eapply record_frame_right_inj with (m1 := m1'); eauto.
    eapply record_frame_left_inj; eauto.
  - intros. exploit mext_perm_inv0.
    eapply perm_record_frame in RECORD; eauto. apply RECORD in H. apply H.
    intros [A|A].
    eapply perm_record_frame in H0; eauto. left. apply H0. auto.
    right; intuition eauto.
    apply A. eapply perm_record_frame in H0; eauto. apply H0. auto.
Qed.
(*
Theorem pop_stage_left_extends : forall m1 m1' m2,
    extends m1 m2 ->
    pop_stage m1 = Some m1' ->
    extends m1' m2.
Proof.
  intros. inv H. constructor.
  - erewrite <- supp_pop_stage; eauto.
  - eapply pop_stage_left_inj; eauto.
  - intros. apply mext_perm_inv0 in H. destruct H.
    left. eapply perm_pop_stage in H0. apply H0. auto.
    right. eapply perm_pop_stage in H0. intro. apply H.
    apply H0. auto.
Qed.

Theorem pop_stage_right_extends' : forall m1 m2 m2',
    extends' m1 m2 ->
    pop_stage m2 = Some m2' ->
    extends' m1 m2'.
Proof.
  intros. inv H. constructor.
  - rewrite <- (supp_pop_stage _ _ H0). auto.
  - eapply pop_stage_right_inj; eauto.
  - intros. eapply mext_perm_inv0.
    rewrite perm_pop_stage; eauto.
Qed.

Theorem push_stage_left_extends' : forall m1 m1' m2,
    extends' m1 m2 ->
    push_stage m1 = m1' ->
    extends' m1' m2.
Proof.
  intros. inv H. constructor; eauto.
  eapply push_stage_left_inj; eauto.
Qed.

Lemma push_stage_right_extends' : forall m1 m2,
    Mem.extends' m1 m2 -> Mem.extends' m1 (Mem.push_stage m2).
Proof.
  intros. inv H. constructor; eauto.
  eapply push_stage_right_inj; eauto.
Qed.
*)
Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  unfold nextblock. congruence. subst b'.
  exists m2'; split; auto.
  constructor.
  rewrite (support_alloc _ _ _ _ _ H0).
  rewrite (support_alloc _ _ _ _ _ ALLOC).
  unfold nextblock. congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  lia.
  intros. eapply perm_alloc_inv in H; eauto.
  generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
  destruct (eq_block b0 b).
  subst b0.
  assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; tauto.
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (support_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (support_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. lia.
  intros. eauto using perm_free_3.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by lia.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (support_free _ _ _ _ _ H0).
  rewrite (support_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); lia. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_sup0. tauto.
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

(** * Stack Structure Equality *)

Definition stackseq (m1 m2:mem) :Prop :=
  struct_eq (stack m1.(support)) (stack m2.(support))
  /\ sid (support m1) = sid (support m2).

Theorem alloc_stackseq : forall m1 lo hi b m1',
    alloc m1 lo hi = (m1',b) ->
    stackseq m1 m1'.
Proof.
  intros. inv H. unfold stackseq. simpl.
  unfold sup_incr. destruct (next_block_stree (stack(support m1))) eqn:?.
  destruct p. destruct p.
  apply next_block_stree_struct_eq in Heqp.
  unfold stack in *. simpl. rewrite setstack_stack. auto. apply sid_valid.
Qed.

Theorem store_stackseq : forall chunk m1 b ofs v m2,
    store chunk m1 b ofs v = (Some m2) ->
    stackseq m1 m2.
Proof.
  intros. unfold stackseq.
  rewrite (support_store _ _ _ _ _ _ H).
  split. apply struct_eq_refl. auto.
Qed.

Theorem store_parallel_stackseq :
  forall chunk1 m1 b1 ofs1 v1 m1' chunk2 m2 b2 ofs2 v2 m2',
    store chunk1 m1 b1 ofs1 v1 = Some m1' ->
    store chunk2 m2 b2 ofs2 v2 = Some m2' ->
    stackseq m1 m2 ->
    stackseq m1' m2'.
Proof.
  intros. unfold stackseq in *.
  rewrite (support_store _ _ _ _ _ _ H).
  rewrite (support_store _ _ _ _ _ _ H0).
  congruence.
Qed.

Theorem alloc_parallel_stackseq :
  forall m1 m2 lo1 hi1 lo2 hi2 b1 b2 m1' m2',
    alloc m1 lo1 hi1 = (m1',b1) ->
    alloc m2 lo2 hi2 = (m2',b2) ->
    stackseq m1 m2 ->
    stackseq m1' m2'.
Proof.
  intros.
  apply alloc_stackseq in H. inv H.
  apply alloc_stackseq in H0. inv H0. inv H1. split.
  eapply struct_eq_trans; eauto.
  eapply struct_eq_trans; eauto.
  eapply struct_eq_comm; eauto. congruence.
Qed.

Theorem alloc_frame_parallel_stackseq :
  forall m1 m2 m1' m2' id p1 p2,
    stackseq m1 m2 ->
    alloc_frame m1 id = (m1',p1) ->
    alloc_frame m2 id = (m2',p2) ->
    p1 = p2 /\
    stackseq m1'  m2'.
Proof.
  intros.
  apply support_alloc_frame in H0 as H2.
  apply support_alloc_frame in H1 as H3.
  unfold sup_incr_frame in *. destr_in H2. destr_in H3.
  inversion H.
  exploit next_stree_struct_eq; eauto.
  intros [A B]. split.
  - rewrite (path_alloc_frame _ _ _ _ H0).
    rewrite (path_alloc_frame _ _ _ _ H1).
    unfold sup_npath. unfold npath. repeat destr.
  - unfold stackseq. rewrite H2. rewrite H3. simpl.
    unfold stack. simpl. repeat rewrite setstack_stack.
    auto. apply sid_valid. apply sid_valid.
Qed.

Theorem return_frame_parallel_stackseq :
  forall m1 m2 m1',
    stackseq m1 m2 ->
    return_frame m1 = Some m1' ->
    exists m2',
    return_frame m2 = Some m2' /\
    stackseq m1' m2'.
Proof.
  intros.
  apply support_return_frame in H0 as H1. unfold sup_return_frame in H1.
  repeat destr_in H1. inversion H.
  exploit return_stree_struct_eq; eauto.
  intros (s2' & A & B).
  unfold return_frame. apply return_frame_active in H0.
  apply active_struct_eq in H1. apply H1 in H0.
  destr. eexists. split. eauto. unfold stackseq.
  simpl. unfold sup_return_frame'. unfold sup_return_frame.
  rewrite A. inv H3. simpl.
  unfold stack. simpl. repeat rewrite setstack_stack.
  auto. apply sid_valid. apply sid_valid.
Qed.

Lemma stackseq_id_path : forall m1 m2 fid1 p1 pos1 fid2 p2 pos2 sid,
    stackseq m1 m2 ->
    nextblock m1 = Stack sid fid1 p1 pos1 ->
    nextblock m2 = Stack sid fid2 p2 pos2 ->
    fid1 = fid2 /\ p1 = p2.
Proof.
  intros. unfold nextblock in *. unfold fresh_block in *.
  destruct (next_block_stree (stack (support m1))) eqn:?.
  destruct p. destruct p. inv H0.
  destruct (next_block_stree (stack (support m2))) eqn:?.
  destruct p. destruct p. inv H1. inversion H.
  exploit struct_eq_next_block_stree; eauto.
Qed.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
Definition inject := inject'.

Local Hint Resolve mi_mappedblocks: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (sup_dec b1 (support m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

Theorem perm_inject_inv:
  forall f m1 m2 b1 ofs b2 delta k p,
  inject f m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

Theorem range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto.
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). lia.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite Ptrofs.unsigned_repr; lia.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
Qed.

Theorem disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try lia.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. lia.
  instantiate (1 := x - delta2). apply H3. lia.
  intuition.
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by lia.
  assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
  rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. lia. congruence.
  exploit valid_access_inject; eauto. intros [C D].
  congruence.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H4; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
Qed.

Theorem storebytes_empty_inject:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem push_stage_inject:
  forall f m1 m2,
    inject f m1 m2 ->
    inject f (push_stage m1) (push_stage m2).
Proof.
  intros. inversion H. constructor; auto.
  - inv mi_inj0. constructor; auto.
Qed.

Theorem push_stage_left_inject:
  forall f m1 m2,
    inject f m1 m2 ->
    inject f (push_stage m1) m2.
Proof.
  intros. inv H. constructor; auto.
  inv mi_inj0. constructor; auto.
Qed.

Theorem push_stage_right_inject:
  forall f m1 m2,
    inject f m1 m2 ->
    inject f m1 (push_stage m2).
Proof.
  intros. inv H. constructor; auto.
  inv mi_inj0. constructor; auto.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto.
  eapply mi_perm_inv0; eauto.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
  exists f'; split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  intros. unfold f'. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* no overlap *)
  unfold f'; red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap0. eexact H3. eauto. eauto.
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1); try discriminate.
  eapply mi_representable0; try eassumption.
  destruct H4; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
  exploit mi_perm_inv0; eauto.
  intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image *)
  split. unfold f'; apply dec_eq_true.
(* incr *)
  intros; unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). lia.
  eapply mi_representable0; try eassumption.
  destruct H10; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_frame_parallel_inject :
  forall f m1 m2 id m1' p1,
    inject f m1 m2 ->
    alloc_frame m1 id = (m1',p1) ->
    exists m2' p2, alloc_frame m2 id = (m2',p2) /\
    inject f m1' m2'.
Proof.
  intros. case_eq (alloc_frame m2 id). intros. exists m,p.
  split. auto.
  inv H0. inv H1. inv H.
  constructor; eauto.
  - inv mi_inj0. constructor; eauto.
  - unfold valid_block. simpl. intros.
    apply mi_freeblocks0. intro. apply H.
    apply sup_incr_frame_in. auto.
  - unfold valid_block in *. simpl.
    intros. exploit mi_mappedblocks0; eauto.
    apply sup_incr_frame_in.
Qed.

Theorem alloc_frame_left_inject :
  forall f m1 m2 m1' id p1,
    inject f m1 m2 ->
    alloc_frame m1 id = (m1',p1) ->
    inject f m1' m2.
Proof.
  intros. inv H. inv H0.
  constructor; eauto.
  - inv mi_inj0. constructor; eauto.
  - unfold valid_block. simpl. intros.
    apply mi_freeblocks0. intro. apply H.
    apply sup_incr_frame_in. auto.
Qed.

Theorem return_frame_inject :
  forall f m1 m2 m1' m2',
    inject f m1 m2 ->
    return_frame m1 = Some m1' ->
    return_frame m2 = Some m2' ->
    inject f m1' m2'.
Proof.
  intros. unfold return_frame in *.
  destr_in H0. inv H0. destr_in H1. inv H1.
  inv H. inv mi_inj0.
  constructor; eauto.
  constructor; eauto.
  unfold valid_block in *. simpl in *. eauto. intros. eapply mi_freeblocks0.
  intro. apply H. apply sup_return_frame_in with (s := support m1); eauto.
  apply sup_return_refl'. auto.
  unfold valid_block in *. simpl in *. eauto. intros. exploit mi_mappedblocks0.
  apply H. apply sup_return_frame_in with (s := support m2); eauto.
  apply sup_return_refl'. auto.
Qed.

Theorem return_frame_right_inject :
  forall f m1 m2 m2',
    inject f m1 m2 ->
    return_frame m2 = Some m2' ->
    inject f m1 m2'.
Proof.
  intros.
  unfold return_frame in H0.
  destr_in H0. inversion H0. inversion H.
  constructor; auto.  inv mi_inj0.
  constructor; eauto.
  unfold valid_block in *. simpl in *. eauto. intros. exploit mi_mappedblocks0.
  apply H1. apply sup_return_frame_in with (s := support m2); eauto.
  apply sup_return_refl'. auto.
Qed.

Theorem return_frame_left_inject :
  forall f m1 m2 m1',
    inject f m1 m2 ->
    return_frame m1 = Some m1' ->
    inject f m1' m2.
Proof.
  intros.
  unfold return_frame in H0.
  destr_in H0. inversion H0. inversion H.
  constructor; auto.  inv mi_inj0.
  constructor; eauto.
  unfold valid_block in *. simpl in *. eauto. intros. eapply mi_freeblocks0.
  intro. apply H1. apply sup_return_frame_in with (s := support m1); eauto.
  apply sup_return_refl'. auto.
Qed.

Theorem return_frame_parallel_inject :
  forall f m1 m2 m1',
    inject f m1 m2 ->
    return_frame m1 = Some m1' ->
    is_active (stack(support m2)) ->
    exists m2',
      return_frame m2 = Some m2' /\ inject f m1' m2'.
Proof.
  intros.
  apply active_return_frame in H1. destruct H1 as [m2' H1].
  exists m2'. split. auto. unfold return_frame in *.
  destr_in H0. inv H0. destr_in H1. inv H1.
  inv H. constructor; eauto.
  - inv mi_inj0. constructor; eauto.
  - unfold valid_block. simpl. intros.
    apply mi_freeblocks0. intro. apply H.
    apply sup_return_frame_in with (s := support m1); eauto.
    apply sup_return_refl'. auto.
  - unfold valid_block in *. simpl.
    intros. exploit mi_mappedblocks0; eauto.
    apply sup_return_frame_in with (s := support m2); eauto.
    apply sup_return_refl'. auto.
Qed.

Theorem alloc_parallel_stackeq :
  forall m1 m2 lo1 hi1 lo2 hi2 b1 b2 m1' m2',
    alloc m1 lo1 hi1 = (m1',b1) ->
    alloc m2 lo2 hi2 = (m2',b2) ->
    stackeq m1 m2 ->
    stackeq m1' m2' /\ b1 = b2.
Proof.
  intros. inv H. inv H0. inversion H1.
  simpl. unfold sup_incr. split. split; simpl.
  rewrite H. simpl.
  destruct (next_block_stree (stack(support m2))).
  unfold stack. simpl. repeat rewrite setstack_stack.
  auto. apply sid_valid. apply sid_valid.
  rewrite H. destr.
  apply stackeq_nextblock. auto.
Qed.

Theorem alloc_parallel_astackeq:
  forall m1 m2 lo1 hi1 lo2 hi2 b1 b2 m1' m2',
    alloc m1 lo1 hi1 = (m1',b1) ->
    alloc m2 lo2 hi2 = (m2',b2) ->
    astack(support m1) = astack(support m2) ->
    astack(support m1') = astack (support m2').
Proof.
  intros. inv H; inv H0. simpl. unfold sup_incr. simpl.
  destr; destr; reflexivity.
Qed.

Theorem alloc_frame_parallel_stackeq :
  forall m1 m2 id m1' m2' p1 p2,
    alloc_frame m1 id = (m1',p1) ->
    alloc_frame m2 id = (m2',p2) ->
    stackeq m1 m2 ->
    stackeq m1' m2' /\ p1 = p2.
Proof.
  intros. inversion H1. split. unfold stackeq.
  rewrite (support_alloc_frame _ _ _ _ H).
  rewrite (support_alloc_frame _ _ _ _ H0).
  unfold sup_incr_frame.
  rewrite H2. destruct (next_stree (stack (support m2))).
  unfold stack. simpl. repeat rewrite setstack_stack.
  auto. apply sid_valid. apply sid_valid.
  rewrite (path_alloc_frame _ _ _ _ H).
  rewrite (path_alloc_frame _ _ _ _ H0).
  unfold sup_npath. unfold npath. rewrite H2. reflexivity.
Qed.

Theorem return_frame_parallel_stackeq :
  forall m1 m2 m1' m2',
    return_frame m1 = Some m1' ->
    return_frame m2 = Some m2' ->
    stackeq m1 m2 ->
    stackeq m1' m2'.
Proof.
  intros. inversion H1. unfold stackeq.
  apply support_return_frame in H.
  apply support_return_frame in H0.
  unfold sup_return_frame in *.
  rewrite H2 in H.
  destruct (return_stree (stack(support m2))).
  destruct p. inv H. inv H0.
  unfold stack. simpl. repeat rewrite setstack_stack.
  auto. apply sid_valid. apply sid_valid.
  inv H.
Qed.

Theorem alloc_frame_parallel_astackeq :
  forall m1 m2 id m1' m2' p1 p2,
    astack (support m1) = astack (support m2) ->
    alloc_frame m1 id = (m1',p1) ->
    alloc_frame m2 id = (m2',p2) ->
    astack (support m1') = astack (support m2').
Proof.
  intros. inv H0; inv H1; simpl. unfold sup_incr_frame.
  destr; destr; reflexivity.
Qed.

Theorem return_frame_parallel_astackeq :
  forall m1 m2 m1' m2',
    return_frame m1 = Some m1' ->
    return_frame m2 = Some m2' ->
    astack (support m1) = astack (support m2) ->
    astack (support m1') = astack (support m2').
Proof.
  intros.
  apply support_return_frame in H.
  apply support_return_frame in H0.
  unfold sup_return_frame in *.
  repeat destr_in H. repeat destr_in H0. simpl in *.
  unfold astack in *. simpl.
  congruence.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  red; intros. apply Z.divide_0_r.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(* Preservation of [pop_stage] operations *)

Lemma pop_stage_left_inject:
  forall f m1 m2 m1',
    inject f m1 m2 ->
    pop_stage m1 = Some m1' ->
    inject f m1' m2.
Proof.
  intros. inversion H. constructor; auto.
  - eapply pop_stage_left_inj; eauto.
  - eauto with mem.
  - red; intros. eapply mi_no_overlap0; eauto.
    rewrite perm_pop_stage. apply H4. auto.
    rewrite perm_pop_stage. apply H5. auto.
  - intros. eapply mi_representable0; eauto.
    destruct H2. left.
    rewrite perm_pop_stage; eauto. right.
    rewrite perm_pop_stage; eauto.
  - intros. exploit mi_perm_inv0; eauto. intros [H'|H'].
    left. rewrite <- perm_pop_stage; eauto.
    right. rewrite <- perm_pop_stage; eauto.
Qed.

Lemma pop_stage_right_inject:
  forall f m1 m2 m2',
    inject f m1 m2 ->
    pop_stage m2 = Some m2' ->
    inject f m1 m2'.
Proof.
  intros. inversion H. constructor; eauto.
  eapply pop_stage_right_inj; eauto.
  intros. eauto with mem.
  intros. rewrite <- perm_pop_stage in H2; eauto.
Qed.

Theorem pop_stage_parallel_inject:
  forall f m1 m2 m1',
  inject f m1 m2 ->
  pop_stage m1 = Some m1' ->
  astack(support m2) <> nil ->
  exists m2', pop_stage m2 = Some m2' /\
  inject f m1' m2'.
Proof.
  intros. inversion H.
  destruct (nonempty_pop_stage _ H1) as [m2' POP].
  exists m2'. split. auto.
  constructor; auto.
  - eapply pop_stage_right_inj with (m1 := m1'); eauto.
    eapply pop_stage_left_inj; eauto.
  - eauto with mem.
  - eauto with mem.
  - red. intros.
    rewrite <- perm_pop_stage in H5; eauto.
    rewrite <- perm_pop_stage in H6; eauto.
  - intros. eapply mi_representable0; eauto.
    destruct H3. left. rewrite perm_pop_stage; eauto.
    right. rewrite perm_pop_stage; eauto.
  - intros. exploit mi_perm_inv0; eauto.
    rewrite <- perm_pop_stage in H3; eauto. intros [A|A].
    left. rewrite <- perm_pop_stage; eauto.
    right. rewrite <- perm_pop_stage; eauto.
Qed.

Lemma record_frame_left_inject:
  forall f m1 m2 m1' fr,
    inject f m1 m2 ->
    record_frame m1 fr = Some m1' ->
    inject f m1' m2.
Proof.
  intros. inversion H. constructor; auto.
  - eapply record_frame_left_inj; eauto.
  - eauto with mem.
  - red; intros. eapply mi_no_overlap0; eauto.
    rewrite perm_record_frame; eauto.
    rewrite perm_record_frame; eauto.
  - intros. eapply mi_representable0; eauto.
    destruct H2. left.
    rewrite perm_record_frame; eauto. right.
    rewrite perm_record_frame; eauto.
  - intros. exploit mi_perm_inv0; eauto. intros [H'|H'].
    left. rewrite <- perm_record_frame; eauto.
    right. rewrite <- perm_record_frame; eauto.
Qed.

Lemma record_frame_right_inject:
  forall f m1 m2 m2' fr,
    inject f m1 m2 ->
    record_frame m2 fr = Some m2' ->
    inject f m1 m2'.
Proof.
  intros. inversion H. constructor; eauto.
  eapply record_frame_right_inj; eauto.
  intros. eauto with mem.
  intros. rewrite <- perm_record_frame in H2; eauto.
Qed.

Theorem record_frame_parallel_inject:
  forall f m1 m2 m1' fr ,
  inject f m1 m2 ->
  record_frame m1 fr = Some m1' ->
  astack(support m2) <> nil ->
  stack_size (astack(support m2)) <= stack_size(astack(support m1)) ->
  exists m2', record_frame m2 fr = Some m2' /\
  inject f m1' m2'.
Proof.
  intros. inversion H.
  eapply request_record_frame in H1; eauto.
  destruct H1 as [m2' RECORD].
  exists m2'. split. eauto.
  constructor; auto.
  - eapply record_frame_right_inj with (m1 := m1'); eauto.
    eapply record_frame_left_inj; eauto.
  - eauto with mem.
  - eauto with mem.
  - red. intros.
    rewrite <- perm_record_frame in H5; eauto.
    rewrite <- perm_record_frame in H6; eauto.
  - intros. eapply mi_representable0; eauto.
    destruct H3. left. rewrite perm_record_frame; eauto.
    right. rewrite perm_record_frame; eauto.
  - intros. exploit mi_perm_inv0; eauto.
    rewrite <- perm_record_frame in H3; eauto. intros [A|A].
    left. rewrite <- perm_record_frame; eauto.
    right. rewrite <- perm_record_frame; eauto.
  - apply record_frame_size1 in H0. lia.
Qed.


(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable0; try eassumption.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Theorem free_parallel_inject:
  forall f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f m1' m2'.
Proof.
  intros.
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta)) as [m2' FREE].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite H0; auto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H2; inv H2.
  exists lo, hi; split; auto with coqlib. lia.
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. lia.
  intros [A|A]. congruence. lia.
Qed.



Lemma drop_outside_inject: forall f m1 m2 b lo hi p m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite support_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

(** Composing two memory injections. *)

Lemma mem_inj_compose:
  forall f f' m1 m2 m3,
  mem_inj f m1 m2 -> mem_inj f' m2 m3 -> mem_inj (compose_meminj f f') m1 m3.
Proof.
  intros. unfold compose_meminj. inv H; inv H0; constructor; intros.
  (* perm *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eauto.
  (* align *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  apply Z.divide_add_r.
  eapply mi_align0; eauto.
  eapply mi_align1 with (ofs := ofs + delta') (p := p); eauto.
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by lia.
  eapply mi_perm0; eauto. apply H0. lia.
  (* memval *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eapply memval_inject_compose; eauto.
Qed.

Theorem inject_compose:
  forall f f' m1 m2 m3,
  inject f m1 m2 -> inject f' m2 m3 ->
  inject (compose_meminj f f') m1 m3.
Proof.
  unfold compose_meminj; intros.
  inv H; inv H0. constructor.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; lia.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H2. eauto.
    eapply perm_inj. eauto. eexact H3. eauto.
  intuition lia.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
  exploit mi_representable1. eauto. instantiate (1 := ofs').
  rewrite H.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by lia.
  destruct H0; eauto using perm_inj.
  rewrite H. lia.
(* perm inv *)
  intros.
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by lia.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

Lemma extends_inject_compose:
  forall f m1 m2 m3,
  extends m1 m2 -> inject f m2 m3 -> inject f m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
(* representable *)
  eapply mi_representable0; eauto.
  destruct H1; eauto using perm_extends.
(* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

Lemma inject_extends_compose:
  forall f m1 m2 m3,
  inject f m1 m2 -> extends m2 m3 -> inject f m1 m3.
Proof.
  intros. inv H; inversion H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. lia.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; subst; inv H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

(** Injecting a memory into itself. *)

Definition flat_inj (s: sup) : meminj :=
  fun (b: block) => if sup_dec b s then Some(b, 0) else None.

Definition inject_neutral (s: sup) (m: mem) :=
  mem_inj (flat_inj s) m m.

Remark flat_inj_no_overlap:
  forall s m, meminj_no_overlap (flat_inj s) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (sup_dec b1 s); inversion H0; subst.
  destruct (sup_dec b2 s); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (support m) m -> inject (flat_inj (support m)) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (sup_dec b (support m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (sup_dec b (support m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); lia.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (sup_dec b1 (support m)); inv H0.
  rewrite Z.add_0_r in H1; auto.
Qed.

Theorem empty_inject_neutral:
  forall s, inject_neutral s empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (sup_dec b1 s); inv H.
  replace (ofs + 0) with ofs by lia; auto.
(* align *)
  unfold flat_inj; intros. destruct (sup_dec b1 s); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. unfold NMap.get. rewrite ! NMap.gi. rewrite ! ZMap.gi. constructor.
Qed.

Theorem alloc_inject_neutral:
  forall s m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral s m ->
  sup_include (sup_incr (support m)) s ->
  inject_neutral s m'.
Proof.
  intros; red.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  unfold flat_inj. apply pred_dec_true.
  apply alloc_result in H. subst.
  apply H1. apply sup_incr_in1.
Qed.

Theorem alloc_glob_inject_neutral:
  forall s m lo hi b m' id,
  alloc_glob id m lo hi = (m', b) ->
  inject_neutral s m ->
  sup_include (sup_incr_glob id (support m)) s ->
  inject_neutral s m'.
Proof.
  intros; red.
  constructor.
  - intros. unfold flat_inj in H2.
    destruct (sup_dec b1 s). inv H2.
    replace (ofs + 0) with ofs by lia. auto. inv H2.
  - intros. unfold flat_inj in H2.
    destruct (sup_dec b1 s). inv H2.
    replace (ofs + 0) with ofs by lia. apply Z.divide_0_r. inv H2.
  - intros. unfold flat_inj in H2.
    destruct (sup_dec b1 s). inv H2.  2: inv H2.
    inv H0. inversion H. simpl. subst. destruct (eq_block b2 (Global id)).
    subst.
    setoid_rewrite NMap.gss.
    replace (ofs + 0) with ofs by lia.
    rewrite ZMap.gi. constructor.
    setoid_rewrite NMap.gso; eauto.
    assert (flat_inj s b2 = Some (b2,0)).
    unfold flat_inj. rewrite pred_dec_true. auto. auto.
    apply mi_memval0; auto.
    replace (ofs) with (ofs +0) by lia.
    eapply mi_perm0. eauto.
    inv H. unfold perm. unfold perm in H3. simpl in H3.
    assert ((NMap.set (Z->perm_kind -> option permission) (Global id)
           (fun (ofs : Z) (_:perm_kind) => if zle lo ofs && zlt ofs hi then
           Some Freeable else None) (mem_access m)) # b2 =
            (mem_access m) # b2).
    apply NMap.gso. auto.
    rewrite H in H3. auto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' s,
  store chunk m b ofs v = Some m' ->
  inject_neutral s m ->
  sup_In b s->
  Val.inject (flat_inj s) v v ->
  inject_neutral s m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by lia.
  intros [m'' [A B]]. congruence.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' s,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral s m ->
  sup_In b s ->
  inject_neutral s m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; eauto.
  repeat rewrite Z.add_0_r. intros [m'' [A B]]. congruence.
Qed.

Section MEMIFF.

Record iff (m1 m2: mem) : Prop := mk_iff {
  sid_iff:
    sid (support m1) = sid (support m2);
  global_iff:
    Mem.global (Mem.support m1) = Mem.global (Mem.support m2);
  stack_iff:
    Mem.stack (Mem.support m1) = Mem.stack (Mem.support m2);
  access_iff:
    m1.(Mem.mem_access) = m2.(Mem.mem_access);
  contents_iff:
    m1.(Mem.mem_contents) = m2.(Mem.mem_contents)
}.

Lemma iff_refl:
  forall m, iff m m.
Proof.
  intros. constructor; auto. Qed.

Lemma iff_comm:
  forall m1 m2, iff m1 m2 -> iff m2 m1.
Proof.
  intros. inv H. constructor; auto.
Qed.

Lemma iff_trans:
  forall m1 m2 m3, iff m1 m2 -> iff m2 m3 -> iff m1 m3.
Proof.
  intros. inv H. inv H0.
  constructor; congruence.
Qed.

Lemma valid_block_iff:
  forall m m' b,
  iff m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. destruct b; simpl in *. erewrite <- sid_iff.
  erewrite <- stack_iff; eauto. auto.  erewrite <- global_iff; eauto.
Qed.

Lemma perm_iff:
  forall m m' b ofs k p,
  iff m m' ->
  perm m b ofs k p <-> perm m' b ofs k p.
Proof.
  intros. destruct H. unfold perm. rewrite access_iff0.
  reflexivity.
Qed.


Lemma range_perm_iff:
  forall m m' b lo hi k p,
    iff m m' ->
    range_perm m b lo hi k p = range_perm m' b lo hi k p.
Proof.
  unfold range_perm. intros.
  inv H.
  unfold perm. rewrite access_iff0.
  auto.
Qed.

Lemma valid_access_iff:
  forall m1 m2 chunk b ofs p,
    iff m1 m2 ->
    valid_access m1 chunk b ofs p <-> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H.
  unfold valid_access.
  unfold range_perm.
  unfold perm.
  rewrite access_iff0. reflexivity.
Qed.

Lemma load_iff:
  forall m1 m2 chunk b ofs,
    iff m1 m2 ->
    load chunk m1 b ofs = load chunk m2 b ofs.
Proof.
  intros. inversion H. unfold load.
  destruct (valid_access_dec m1 chunk b ofs Readable).
  - rewrite pred_dec_true. rewrite contents_iff0. reflexivity.
    rewrite <- valid_access_iff; eauto.
  - rewrite pred_dec_false. auto.
    rewrite <- valid_access_iff; eauto.
Qed.

Lemma loadv_iff:
  forall m1 m2 chunk  addr,
    iff m1 m2 ->
    loadv chunk m1 addr = loadv chunk m2 addr.
Proof.
  intros. inversion H. unfold loadv.
  destruct addr; eauto.
  apply load_iff. eauto.
Qed.

Lemma loadbytes_iff:
  forall m1 m2 b ofs n,
    iff m1 m2 ->
    loadbytes m1 b ofs n = loadbytes m2 b ofs n.
Proof.
  intros. inversion H.
  unfold loadbytes.
  repeat destr.
  erewrite range_perm_iff in r; eauto. congruence.
  erewrite <- range_perm_iff in r; eauto. congruence.
Qed.

Lemma store_iff:
  forall m1 m2 m1' chunk b ofs v,
    iff m1 m2 ->
    store chunk m1 b ofs v = Some m1' ->
    exists m2',
      store chunk m2 b ofs v = Some m2'
      /\ iff m1' m2'.
Proof.
  intros m1 m2 m1' chunk b ofs v IFF STORE.
  inversion IFF.
  apply store_valid_access_3 in STORE as VALID.
  apply store_valid_access_3 in STORE as VALID'.
  erewrite valid_access_iff in VALID'; eauto.
  eapply valid_access_store in VALID' as X.
  destruct X as [m2' STORE'].
  exists m2'. split. eauto.
  unfold store in *.
  rewrite pred_dec_true in STORE; eauto.
  rewrite pred_dec_true in STORE'; eauto.
  inv STORE. inv STORE'.
  constructor; auto. simpl.
  rewrite contents_iff0. auto.
Qed.

Lemma storev_iff:
  forall m1 m2 m1' chunk addr v,
    iff m1 m2 ->
    storev chunk m1 addr v = Some m1' ->
    exists m2',
      storev chunk m2 addr v = Some m2'
      /\ iff m1' m2'.
Proof.
  intros m1 m2 m1' chunk addr v IFF.
  unfold storev. destruct addr; try congruence; eauto.
  apply store_iff. auto.
Qed.

Lemma storebytes_iff:
  forall m1 m2 m1' b ofs bytes,
    iff m1 m2 ->
    storebytes m1 b ofs bytes = Some m1' ->
    exists m2',
      storebytes m2 b ofs bytes = Some m2'
      /\ iff m1' m2'.
Proof.
  intros. inversion H.
  apply storebytes_range_perm in H0 as PERM.
  apply storebytes_range_perm in H0 as PERM'.
  erewrite range_perm_iff in PERM'; eauto.
  apply range_perm_storebytes in PERM' as X.
  destruct X as [m2' STORE'].
  exists m2'. split. auto. unfold storebytes in *.
  destr_in H0. inv H0.
  destr_in STORE'. inv STORE'.
  constructor; auto. simpl.
  rewrite contents_iff0. auto.
Qed.

Lemma push_stage_iff:
  forall m, iff m (Mem.push_stage m).
Proof.
  intros. constructor; auto.
Qed.

Lemma pop_stage_iff:
  forall m m', Mem.pop_stage m = Some m' -> iff m m'.
Proof.
  intros. unfold pop_stage in H.
  destruct (astack (support m)). discriminate.
  inv H.
  constructor; auto.
Qed.

Lemma record_frame_iff:
  forall m m' fr, Mem.record_frame m fr = Some m' -> iff m m'.
Proof.
  intros. unfold record_frame in H.
  destr_in H. destr_in H. inv H.
  constructor; auto.
Qed.

Lemma push_stage_right_iff:
  forall m1 m2,
    iff m1 m2 -> iff m1 (Mem.push_stage m2).
Proof.
  intros.
  eapply iff_trans.  eauto.  eapply push_stage_iff.
Qed.

Lemma push_stage_left_iff:
  forall m1 m2,
    iff m1 m2 -> iff (Mem.push_stage m1) m2.
Proof.
  intros.
  eapply iff_trans. eapply iff_comm. eapply push_stage_iff; eauto. eauto.
Qed.

Lemma pop_stage_right_iff:
  forall m1 m2 m2',
    iff m1 m2 -> Mem.pop_stage m2 = Some m2' -> iff m1 m2'.
Proof.
  intros.
  eapply iff_trans. eauto. eapply pop_stage_iff. eauto.
Qed.

Lemma pop_stage_left_iff:
  forall m1 m2 m1',
    iff m1 m2 -> Mem.pop_stage m1 = Some m1' -> iff m1' m2.
Proof.
  intros.
  eapply iff_trans. eapply iff_comm. eapply pop_stage_iff; eauto. eauto.
Qed.

Lemma free_parallel_iff:
  forall m1 m2 m1' b lo hi,
    iff m1 m2 ->
    free m1 b lo hi = Some m1' ->
    exists m2', free m2 b lo hi = Some m2'
           /\ iff m1' m2'.
Proof.
  intros.
  apply free_range_perm in H0 as PERM.
  apply free_range_perm in H0 as PERM'.
  erewrite range_perm_iff in PERM'; eauto.
  eapply range_perm_free in PERM' as X.
  destruct X as [m2' FREE].
  exists m2'. split. auto.
  unfold free in *.
  rewrite pred_dec_true in *; eauto.
  inv H0. inv FREE. unfold unchecked_free.
  inv H. constructor; eauto. simpl.
  rewrite access_iff0. eauto.
Qed.

Lemma alloc_frame_iff :
  forall m1 m2 m1' id path,
    iff m1 m2 ->
    alloc_frame m1 id = (m1',path) ->
    exists m2', alloc_frame m2 id = (m2',path) /\ iff m1' m2'.
Proof.
  intros. inversion H. caseEq (alloc_frame m2 id). intros.
  exists m. split. apply path_alloc_frame in H0.
  apply path_alloc_frame in H1. unfold sup_npath in *. congruence.
  inv H0. inv H1.
  constructor; simpl; auto; unfold sup_incr_frame; rewrite stack_iff0; destr.
  unfold stack in *. simpl. repeat rewrite setstack_stack. auto.
  apply sid_valid. apply sid_valid.
Qed.

Lemma return_frame_iff :
  forall m1 m2 m1',
  iff m1 m2 ->
  return_frame m1 = Some m1' ->
  exists m2', return_frame m2 = Some m2' /\ iff m1' m2'.
Proof.
  intros. inversion H.
  apply return_frame_active in H0 as H1. rewrite stack_iff0 in H1.
  apply active_return_frame in H1 as H2. destruct H2 as [m2' H3].
  exists m2'. split. eauto. unfold return_frame in *. destr_in H0.
  destr_in H3. inv H0. inv H3.
  constructor; simpl; auto;  unfold sup_return_frame';
  unfold sup_return_frame.
  rewrite stack_iff0. destruct (return_stree (stack (support m2))) eqn:?. destruct p. simpl. auto. auto.
  rewrite stack_iff0. destruct (return_stree (stack (support m2))) eqn:?. destruct p. simpl. auto. auto.
  rewrite stack_iff0. destruct (return_stree (stack (support m2))) eqn:?. destruct p.   unfold stack in *. simpl. repeat rewrite setstack_stack. auto.
  apply sid_valid. apply sid_valid. auto.
Qed.

Lemma alloc_parallel_iff:
  forall m1 m2 m1' lo hi b,
    iff m1 m2 ->
    alloc m1 lo hi = (m1',b) ->
    exists m2', alloc m2 lo hi = (m2',b)
           /\ iff m1' m2'.
Proof.
  intros.  inversion H.
  caseEq (alloc m2 lo hi).
  intros.
  assert (b = b0).
   apply alloc_result in H0.
   apply alloc_result in H1.
  unfold nextblock in *. unfold fresh_block in *.
  rewrite stack_iff0 in H0. rewrite sid_iff0 in H0. congruence.
  subst.
  exists m. split. auto.
  unfold alloc in *. inv H0. inv H1.
  constructor; simpl; try congruence; unfold sup_incr;
  rewrite stack_iff0; destr.
  unfold stack in *. simpl. repeat rewrite setstack_stack. auto.
  apply sid_valid. apply sid_valid.
Qed.

Lemma pop_stage_safe_iff:
  forall m1 m2 m1' m2',
    iff m1 m2 ->
    pop_stage m1 = Some m1' ->
    pop_stage m2 = Some m2' ->
    iff m1' m2'.
Proof.
  intros.
  eapply iff_trans. eapply iff_comm.
  eapply pop_stage_iff; eauto.
  eapply iff_trans. eauto.
  eapply pop_stage_iff; eauto.
Qed.

Lemma push_stage_safe_iff:
  forall m1 m2,
    iff m1 m2 -> iff (push_stage m1) (push_stage m2).
Proof.
  intros. inv H. constructor; auto.
Qed.


Lemma record_frame_safe_iff:
  forall m1 m2 m1' m2' fr,
    iff m1 m2 ->
    record_frame m1 fr = Some m1' ->
    record_frame m2 fr = Some m2' ->
    iff m1' m2'.
Proof.
  intros.
  eapply iff_trans. eapply iff_comm.
  eapply record_frame_iff; eauto.
  eapply iff_trans. eauto.
  eapply record_frame_iff; eauto.
Qed.

End MEMIFF.


(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_support:
    sup_include (support m_before) (support m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (NMap.get _ b m_after.(mem_contents)) =
    ZMap.get ofs (NMap.get _ b m_before.(mem_contents))
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. apply sup_include_refl. tauto. tauto.
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_support in H. auto.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto.
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply sup_include_trans with (support m2); apply unchanged_on_support; auto.
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto.
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite Z2Nat.id in H by lia.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). lia.
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b ofs,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_store _ _ _ _ _ _ H). apply sup_include_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). lia. auto.
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_storebytes _ _ _ _ _ H). apply sup_include_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z.of_nat (length bytes))); auto.
  elim (H0 ofs0). lia. auto.
Qed.

Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_alloc _ _ _ _ _ H). intro. intro. apply sup_incr_in2. auto.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_free _ _ _ _ _ H). apply sup_include_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

Lemma drop_perm_unchanged_on:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_drop _ _ _ _ _ _ H). apply sup_include_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0.
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; lia.
  eapply perm_drop_4; eauto.
- unfold drop_perm in H.
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto.
Qed.

End UNCHANGED_ON.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto.
- apply unchanged_on_contents0; auto.
  apply H0; auto. eapply perm_valid_block; eauto.
Qed.

End Mem.

Notation mem := Mem.mem.
Notation sup := Mem.sup.
Notation sup_In := Mem.sup_In.
Notation sup_incr := Mem.sup_incr.
Notation sup_incr_glob := Mem.sup_incr_glob.
Notation sup_init := Mem.sup_init.
Notation fresh_block := Mem.fresh_block.
Notation freshness := Mem.freshness.
Global Opaque Mem.alloc Mem.alloc_glob Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Hint Resolve Mem.sup_incr_in1 Mem.sup_incr_in2 : core.
Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
: mem.

