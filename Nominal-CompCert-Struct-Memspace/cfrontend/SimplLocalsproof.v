(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Semantic preservation for the SimplLocals pass. *)

Require Import FSets.
Require Import Coqlib Errors Ordered Maps Integers Floats.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Ctypes Cop Clight SimplLocals.

Module VSF := FSetFacts.Facts(VSet).
Module VSP := FSetProperties.Properties(VSet).

Definition match_prog (p tp: program) : Prop :=
    match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp
 /\ prog_types tp = prog_types p.

Lemma match_transf_program:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold transf_program; intros. monadInv H.
  split; auto. apply match_transform_partial_program. rewrite EQ. destruct x; auto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Lemma comp_env_preserved:
  genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. destruct TRANSF as [_ EQ]. simpl in EQ. congruence.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match (proj1 TRANSF)).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match (proj1 TRANSF)).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial (proj1 TRANSF)).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial (proj1 TRANSF)).

Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. simpl; unfold type_of_function; simpl. auto.
Qed.

(** Matching between environments before and after *)

Inductive match_var (f: meminj) (cenv: compilenv) (e: env) (m: mem) (te: env) (tle: temp_env) (id: ident) : Prop :=
  | match_var_lifted: forall b ty chunk v tv
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = true)
      (MAPPED: f b = None)
      (MODE: access_mode ty = By_value chunk)
      (LOAD: Mem.load chunk m b 0 = Some v)
      (TLENV: tle!(id) = Some tv)
      (VINJ: Val.inject f v tv),
      match_var f cenv e m te tle id
  | match_var_not_lifted: forall b ty b'
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = Some(b', ty))
      (LIFTED: VSet.mem id cenv = false)
      (MAPPED: f b = Some(b', 0)),
      match_var f cenv e m te tle id
  | match_var_not_local: forall
      (ENV: e!id = None)
      (TENV: te!id = None)
      (LIFTED: VSet.mem id cenv = false),
      match_var f cenv e m te tle id.

Record match_envs (f: meminj) (cenv: compilenv)
                  (e: env) (le: temp_env) (m: mem) (lo hi: sup)
                  (te: env) (tle: temp_env) (tlo thi: sup) : Prop :=
  mk_match_envs {
    me_vars:
      forall id, match_var f cenv e m te tle id;
    me_temps:
      forall id v,
      le!id = Some v ->
      (exists tv, tle!id = Some tv /\ Val.inject f v tv)
      /\ (VSet.mem id cenv = true -> v = Vundef);
    me_inj:
      forall id1 b1 ty1 id2 b2 ty2, e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    me_range:
      forall id b ty, e!id = Some(b, ty) -> ~ sup_In b lo /\ sup_In b hi;
    me_trange:
      forall id b ty, te!id = Some(b, ty) -> ~ sup_In b tlo  /\ sup_In b thi;
    me_mapped:
      forall id b' ty,
      te!id = Some(b', ty) -> exists b, f b = Some(b', 0) /\ e!id = Some(b, ty);
    me_flat:
      forall id b' ty b delta,
      te!id = Some(b', ty) -> f b = Some(b', delta) -> e!id = Some(b, ty) /\ delta = 0;
    me_incr:
      Mem.sup_include lo hi;
    me_tincr:
      Mem.sup_include tlo thi
  }.

(** Invariance by change of memory and injection *)

Lemma match_envs_invariant:
  forall f cenv e le m lo hi te tle tlo thi f' m',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  (forall b chunk v,
    f b = None -> ~ sup_In b lo /\ sup_In b hi -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  inject_incr f f' ->
  (forall b, ~ sup_In b lo /\ sup_In b hi -> f' b = f b) ->
  (forall b b' delta, f' b = Some(b', delta) -> ~ sup_In b' tlo /\ sup_In b' thi -> f' b = f b) ->
  match_envs f' cenv e le m' lo hi te tle tlo thi.
Proof.
  intros until m'; intros ME LD INCR INV1 INV2.
  destruct ME; constructor; eauto.
(* vars *)
  intros. generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_lifted; eauto.
  rewrite <- MAPPED; eauto.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [[v' [A B]] C]. split; auto. exists v'; eauto.
(* mapped *)
  intros. exploit me_mapped0; eauto. intros [b [A B]]. exists b; split; auto.
(* flat *)
  intros. eapply me_flat0; eauto. rewrite <- H0. symmetry. eapply INV2; eauto.
Qed.

(** Invariance by external call *)

Lemma match_envs_extcall:
  forall f cenv e le m lo hi te tle tlo thi tm f' m',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  Mem.unchanged_on (loc_unmapped f) m m' ->
  inject_incr f f' ->
  inject_separated f f' m tm ->
  Mem.sup_include hi (Mem.support m) -> Mem.sup_include thi (Mem.support tm) ->
  match_envs f' cenv e le m' lo hi te tle tlo thi.
Proof.
  intros. eapply match_envs_invariant; eauto.
  intros. eapply Mem.load_unchanged_on; eauto.
  red in H2. intros. destruct (f b) as [[b' delta]|] eqn:?.
  eapply H1; eauto.
  destruct (f' b) as [[b' delta]|] eqn:?; auto.
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  destruct H5. apply H3 in H6. congruence.
  intros. destruct (f b) as [[b'' delta']|] eqn:?. eauto.
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  destruct H6. apply H4 in H7. congruence.
Qed.

(** Properties of values resulting from a cast *)

Lemma val_casted_load_result:
  forall v ty chunk,
  val_casted v ty -> access_mode ty = By_value chunk ->
  Val.load_result chunk v = v.
Proof.
  intros. inversion H; clear H; subst v ty; simpl in H0.
- destruct sz.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  destruct si; inversion H0; clear H0; subst chunk; simpl in *; congruence.
  clear H1. inv H0. auto.
  inversion H0; clear H0; subst chunk. simpl in *.
  destruct (Int.eq n Int.zero); subst n; reflexivity.
- inv H0; auto.
- inv H0; auto.
- inv H0; auto.
- inv H0. unfold Mptr, Val.load_result; destruct Archi.ptr64; auto. 
- inv H0. unfold Mptr, Val.load_result; rewrite H1; auto.
- inv H0. unfold Val.load_result; rewrite H1; auto.
- inv H0. unfold Mptr, Val.load_result; rewrite H1; auto.
- inv H0. unfold Val.load_result; rewrite H1; auto.
- discriminate.
- discriminate.
- discriminate.
Qed.

Lemma val_casted_inject:
  forall f v v' ty,
  Val.inject f v v' -> val_casted v ty -> val_casted v' ty.
Proof.
  intros. inv H; auto.
  inv H0; constructor; auto.
  inv H0; constructor.
Qed.

Lemma forall2_val_casted_inject:
  forall f vl vl', Val.inject_list f vl vl' ->
  forall tyl, list_forall2 val_casted vl tyl -> list_forall2 val_casted vl' tyl.
Proof.
  induction 1; intros tyl F; inv F; constructor; eauto. eapply val_casted_inject; eauto.
Qed.

Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons  ty1 tyl).

Lemma val_casted_list_params:
  forall params vl,
  val_casted_list vl (type_of_params params) ->
  list_forall2 val_casted vl (map snd params).
Proof.
  induction params; simpl; intros.
  inv H. constructor.
  destruct a as [id ty]. inv H. constructor; auto.
Qed.

(** Correctness of [make_cast] *)

Lemma make_cast_correct:
  forall e le m a v1 tto v2,
  eval_expr tge e le m a v1 ->
  sem_cast v1 (typeof a) tto m = Some v2 ->
  eval_expr tge e le m (make_cast a tto) v2.
Proof.
  intros.
  assert (DFL: eval_expr tge e le m (Ecast a tto) v2).
    econstructor; eauto.
  unfold sem_cast, make_cast in *.
  destruct (classify_cast (typeof a) tto); auto.
  destruct v1; destruct Archi.ptr64; inv H0; auto.
  destruct sz2; auto. destruct v1; inv H0; auto.
  destruct v1; inv H0; auto.
  destruct v1; inv H0; auto.
  destruct v1; inv H0; auto.
  destruct v1; try discriminate.
  destruct (ident_eq id1 id2); inv H0; auto.
  destruct v1; try discriminate.
  destruct (ident_eq id1 id2); inv H0; auto.
  inv H0; auto.
Qed.

(** Debug annotations. *)

Lemma cast_typeconv:
  forall v ty m,
  val_casted v ty ->
  sem_cast v ty (typeconv ty) m = Some v.
Proof.
  induction 1; simpl.
- unfold sem_cast, classify_cast; destruct sz, Archi.ptr64; auto.
- auto.
- auto.
- unfold sem_cast, classify_cast; destruct Archi.ptr64; auto.
- auto.
- unfold sem_cast; simpl; rewrite H; auto.
- unfold sem_cast; simpl; rewrite H; auto.
- unfold sem_cast; simpl; rewrite H; auto.
- unfold sem_cast; simpl; rewrite H; auto.
- unfold sem_cast; simpl. rewrite dec_eq_true; auto.
- unfold sem_cast. simpl. rewrite dec_eq_true; auto.
- auto.
Qed.

Lemma step_Sdebug_temp:
  forall f id ty k e le m v,
  le!id = Some v ->
  val_casted v ty ->
  step2 tge (State f (Sdebug_temp id ty) k e le m)
         E0 (State f Sskip k e le m).
Proof.
  intros. unfold Sdebug_temp. eapply step_builtin with (optid := None).
  econstructor. constructor. eauto. simpl. eapply cast_typeconv; eauto. constructor.
  simpl. constructor.
Qed.

Lemma step_Sdebug_var:
  forall f id ty k e le m b,
  e!id = Some(b, ty) ->
  step2 tge (State f (Sdebug_var id ty) k e le m)
         E0 (State f Sskip k e le m).
Proof.
  intros. unfold Sdebug_var. eapply step_builtin with (optid := None).
  econstructor. constructor. constructor. eauto.
  simpl. reflexivity. constructor.
  simpl. constructor.
Qed.

Lemma step_Sset_debug:
  forall f id ty a k e le m v v',
  eval_expr tge e le m a v ->
  sem_cast v (typeof a) ty m = Some v' ->
  plus step2 tge (State f (Sset_debug id ty a) k e le m)
              E0 (State f Sskip k e (PTree.set id v' le) m).
Proof.
  intros; unfold Sset_debug.
  assert (forall k, step2 tge (State f (Sset id (make_cast a ty)) k e le m)
                           E0 (State f Sskip k e (PTree.set id v' le) m)).
  { intros. apply step_set. eapply make_cast_correct; eauto. }
  destruct (Compopts.debug tt).
- eapply plus_left. constructor.
  eapply star_left. apply H1.
  eapply star_left. constructor.
  apply star_one. apply step_Sdebug_temp with (v := v').
  apply PTree.gss. eapply cast_val_is_casted; eauto.
  reflexivity. reflexivity. reflexivity.
- apply plus_one. apply H1.
Qed.

Lemma step_add_debug_vars:
  forall f s e le m vars k,
  (forall id ty, In (id, ty) vars -> exists b, e!id = Some (b, ty)) ->
  star step2 tge (State f (add_debug_vars vars s) k e le m)
              E0 (State f s k e le m).
Proof.
  unfold add_debug_vars. destruct (Compopts.debug tt).
- induction vars; simpl; intros.
  + apply star_refl.
  + destruct a as [id ty].
    exploit H; eauto. intros (b & TE).
    simpl. eapply star_left. constructor.
    eapply star_left. eapply step_Sdebug_var; eauto.
    eapply star_left. constructor.
    apply IHvars; eauto.
    reflexivity. reflexivity. reflexivity.
- intros. apply star_refl.
Qed.

Remark bind_parameter_temps_inv:
  forall id params args le le',
  bind_parameter_temps params args le = Some le' ->
  ~In id (var_names params) ->
  le'!id = le!id.
Proof.
  induction params; simpl; intros.
  destruct args; inv H. auto.
  destruct a as [id1 ty1]. destruct args; try discriminate.
  transitivity ((PTree.set id1 v le)!id).
  eapply IHparams; eauto. apply PTree.gso. intuition.
Qed.

Lemma step_add_debug_params:
  forall f s k e le m params vl le1,
  list_norepet (var_names params) ->
  list_forall2 val_casted vl (map snd params) ->
  bind_parameter_temps params vl le1 = Some le ->
  star step2 tge (State f (add_debug_params params s) k e le m)
              E0 (State f s k e le m).
Proof.
  unfold add_debug_params. destruct (Compopts.debug tt).
- induction params as [ | [id ty] params ]; simpl; intros until le1; intros NR CAST BIND; inv CAST; inv NR.
  + apply star_refl.
  + assert (le!id = Some a1). { erewrite bind_parameter_temps_inv by eauto. apply PTree.gss. }
    eapply star_left. constructor.
    eapply star_left. eapply step_Sdebug_temp; eauto.
    eapply star_left. constructor.
    eapply IHparams; eauto.
    reflexivity. reflexivity. reflexivity.
- intros; apply star_refl.
Qed.

(** Preservation by assignment to lifted variable. *)

Lemma match_envs_assign_lifted:
  forall f cenv e le m lo hi te tle tlo thi b ty v m' id tv,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  e!id = Some(b, ty) ->
  val_casted v ty ->
  Val.inject f v tv ->
  assign_loc ge ty m b Ptrofs.zero v m' ->
  VSet.mem id cenv = true ->
  match_envs f cenv e le m' lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. destruct H. generalize (me_vars0 id); intros MV; inv MV; try congruence.
  rewrite ENV in H0; inv H0. inv H3; try congruence.
  unfold Mem.storev in H0. rewrite Ptrofs.unsigned_zero in H0.
  constructor; eauto; intros.
(* vars *)
  destruct (peq id0 id). subst id0.
  eapply match_var_lifted with (v := v); eauto.
  exploit Mem.load_store_same; eauto. erewrite val_casted_load_result; eauto.
  apply PTree.gss.
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto.
  rewrite <- LOAD0. eapply Mem.load_store_other; eauto.
  rewrite PTree.gso; auto.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
(* temps *)
  exploit me_temps0; eauto. intros [[tv1 [A B]] C]. split; auto.
  rewrite PTree.gsspec. destruct (peq id0 id).
  subst id0. exists tv; split; auto. rewrite C; auto.
  exists tv1; auto.
Qed.

(** Preservation by assignment to a temporary *)

Lemma match_envs_set_temp:
  forall f cenv e le m lo hi te tle tlo thi id v tv x,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  Val.inject f v tv ->
  check_temp cenv id = OK x ->
  match_envs f cenv e (PTree.set id v le) m lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. unfold check_temp in H1.
  destruct (VSet.mem id cenv) eqn:?; monadInv H1.
  destruct H. constructor; eauto; intros.
(* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso. eauto. congruence.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
(* temps *)
  rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H. split. exists tv; auto. intros; congruence.
  eapply me_temps0; eauto.
Qed.

Lemma match_envs_set_opttemp:
  forall f cenv e le m lo hi te tle tlo thi optid v tv x,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  Val.inject f v tv ->
  check_opttemp cenv optid = OK x ->
  match_envs f cenv e (set_opttemp optid v le) m lo hi te (set_opttemp optid tv tle) tlo thi.
Proof.
  intros. unfold set_opttemp. destruct optid; simpl in H1.
  eapply match_envs_set_temp; eauto.
  auto.
Qed.

(** Extensionality with respect to temporaries *)

Lemma match_envs_temps_exten:
  forall f cenv e le m lo hi te tle tlo thi tle',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  (forall id, tle'!id = tle!id) ->
  match_envs f cenv e le m lo hi te tle' tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite H0; auto.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite H0. eauto.
Qed.

(** Invariance by assignment to an irrelevant temporary *)

Lemma match_envs_change_temp:
  forall f cenv e le m lo hi te tle tlo thi id v,
  match_envs f cenv e le m lo hi te tle tlo thi ->
  le!id = None -> VSet.mem id cenv = false ->
  match_envs f cenv e le m lo hi te (PTree.set id v tle) tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso; auto. congruence.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite PTree.gso. eauto. congruence.
Qed.

(** Properties of [cenv_for]. *)

Definition cenv_for_gen (atk: VSet.t) (vars: list (ident * type)) : compilenv :=
  List.fold_right (add_local_variable atk) VSet.empty vars.

Remark add_local_variable_charact:
  forall id ty atk cenv id1,
  VSet.In id1 (add_local_variable atk (id, ty) cenv) <->
  VSet.In id1 cenv \/ exists chunk, access_mode ty = By_value chunk /\ id = id1 /\ VSet.mem id atk = false.
Proof.
  intros. unfold add_local_variable. split; intros.
  destruct (access_mode ty) eqn:?; auto.
  destruct (VSet.mem id atk) eqn:?; auto.
  rewrite VSF.add_iff in H. destruct H; auto. right; exists m; auto.
  destruct H as [A | [chunk [A [B C]]]].
  destruct (access_mode ty); auto. destruct (VSet.mem id atk); auto. rewrite VSF.add_iff; auto.
  rewrite A. rewrite <- B. rewrite C. apply VSet.add_1; auto.
Qed.

Lemma cenv_for_gen_domain:
 forall atk id vars, VSet.In id (cenv_for_gen atk vars) -> In id (var_names vars).
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. auto.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H.
  destruct H as [A | [chunk [A [B C]]]]; auto.
Qed.

Lemma cenv_for_gen_by_value:
  forall atk id ty vars,
  In (id, ty) vars ->
  list_norepet (var_names vars) ->
  VSet.In id (cenv_for_gen atk vars) ->
  exists chunk, access_mode ty = By_value chunk.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct a as [id1 ty1]. simpl in H0. inv H0.
  rewrite add_local_variable_charact in H1.
  destruct H; destruct H1 as [A | [chunk [A [B C]]]].
  inv H. elim H4. eapply cenv_for_gen_domain; eauto.
  inv H. exists chunk; auto.
  eauto.
  subst id1. elim H4. change id with (fst (id, ty)). apply in_map; auto.
Qed.

Lemma cenv_for_gen_compat:
  forall atk id vars,
  VSet.In id (cenv_for_gen atk vars) -> VSet.mem id atk = false.
Proof.
  induction vars; simpl; intros.
  rewrite VSF.empty_iff in H. contradiction.
  destruct a as [id1 ty1]. rewrite add_local_variable_charact in H.
  destruct H as [A | [chunk [A [B C]]]].
  auto.
  congruence.
Qed.

(** Compatibility between a compilation environment and an address-taken set. *)

Definition compat_cenv (atk: VSet.t) (cenv: compilenv) : Prop :=
  forall id, VSet.In id atk -> VSet.In id cenv -> False.

Lemma compat_cenv_for:
  forall f, compat_cenv (addr_taken_stmt f.(fn_body)) (cenv_for f).
Proof.
  intros; red; intros.
  assert (VSet.mem id (addr_taken_stmt (fn_body f)) = false).
    eapply cenv_for_gen_compat. eexact H0.
  rewrite VSF.mem_iff in H. congruence.
Qed.

Lemma compat_cenv_union_l:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk1 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_2; auto.
Qed.

Lemma compat_cenv_union_r:
  forall atk1 atk2 cenv,
  compat_cenv (VSet.union atk1 atk2) cenv -> compat_cenv atk2 cenv.
Proof.
  intros; red; intros. eapply H; eauto. apply VSet.union_3; auto.
Qed.

Lemma compat_cenv_empty:
  forall cenv, compat_cenv VSet.empty cenv.
Proof.
  intros; red; intros. eapply VSet.empty_1; eauto.
Qed.

Hint Resolve compat_cenv_union_l compat_cenv_union_r compat_cenv_empty: compat.

(** Allocation and initialization of parameters *)

Lemma alloc_variables_stackseq:
  forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  Mem.stackseq m m'.
Proof.
  induction 1.
  apply struct_eq_refl. eapply struct_eq_trans.
  eapply Mem.alloc_stackseq; eauto. eauto.
Qed.

Lemma alloc_variables_parallel_stackseq :
  forall ge1 e1 m1 vars1 e1' m1' ge2 e2 m2 vars2 e2' m2',
  alloc_variables ge1 e1 m1 vars1 e1' m1' ->
  alloc_variables ge2 e2 m2 vars2 e2' m2' ->
  Mem.stackseq m1 m2 ->
  Mem.stackseq m1' m2'.
Proof.
  intros.
  apply alloc_variables_stackseq in H.
  apply alloc_variables_stackseq in H0.
  eapply struct_eq_trans. eapply struct_eq_comm; eauto.
  eapply struct_eq_trans; eauto.
Qed.

Lemma alloc_variables_support:
  forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' -> Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  induction 1.
  apply Mem.sup_include_refl.
  eapply Mem.sup_include_trans; eauto. exploit Mem.support_alloc; eauto. intros EQ. unfold sup_incr in EQ. apply Mem.sup_include_trans with (Mem.support m1). rewrite EQ. apply Mem.sup_include_refl. apply IHalloc_variables.
Qed.

Lemma alloc_variables_range:
  forall ge id b ty e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ ~sup_In b (Mem.support m) /\ sup_In b (Mem.support m').
Proof.
  induction 1; intros.
  auto.
  exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
  destruct (peq id id0). inv A.
  right. exploit Mem.alloc_result; eauto. exploit Mem.support_alloc; eauto.
  generalize (alloc_variables_support _ _ _ _ _ _ H0). intros A B C.
  subst b. split. apply freshness. eapply Mem.sup_include_trans; eauto. apply Mem.sup_include_refl. rewrite B. apply Mem.sup_incr_in1.  auto.
  right. exploit Mem.support_alloc; eauto. intros B. rewrite B in A.
  destruct A.
  split. intro. apply H2. apply Mem.sup_incr_in2.  auto. auto.
Qed.

Lemma alloc_variables_injective:
  forall ge id1 b1 ty1 id2 b2 ty2 e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  (e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2) ->
  (forall id b ty, e!id = Some(b, ty) -> sup_In b (Mem.support m)) ->
  (e'!id1 = Some(b1, ty1) -> e'!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2).
Proof.
  induction 1; intros.
  eauto.
  eapply IHalloc_variables; eauto.
  repeat rewrite PTree.gsspec; intros.
  destruct (peq id1 id); destruct (peq id2 id).
  congruence.
  inv H6. exploit H2; eauto. intros.
  apply Mem.valid_not_valid_diff with m b2 b1 in H6. auto.
  apply Mem.fresh_block_alloc in H. auto.
  inv H7. exploit H2; eauto. intros.
  apply Mem.valid_not_valid_diff with m b1 b2 in H7. auto.
  apply Mem.fresh_block_alloc in H. auto.
  eauto.
  intros. rewrite PTree.gsspec in H6. destruct (peq id0 id). inv H6.
  apply Mem.valid_new_block in H. auto.
  exploit H2; eauto. eapply Mem.valid_block_alloc; eauto.
Qed.

Section SINJ.
Definition posenv := PTree.t positive.
Definition empty_posenv : posenv := PTree.empty positive.

Fixpoint build_penv (ce:compilenv) (vars:list (ident*type)) (idx1 idx2 : positive) : posenv :=
  match vars with
    |nil => empty_posenv
    |(id,ty)::l0 => if VSet.mem id ce then build_penv ce l0 (Pos.succ idx1) (idx2)
                   else (PTree.set idx1 idx2 (build_penv ce l0 (Pos.succ idx1) (Pos.succ idx2)))
  end.

Lemma build_penv_low : forall ce vars idx1 idx2 id,
    (id < idx1)%positive ->
    PTree.get id (build_penv ce vars idx1 idx2) = None.
Proof.
  induction vars; intros; simpl. apply PTree.gempty.
  simpl. destr. destr. apply IHvars. lia.
  rewrite PTree.gso. apply IHvars. lia. lia.
Qed.

Definition find_func_pos (fid:ident)( pos: positive) : option positive:=
  match Genv.find_funct_ptr ge (Global fid) with
    |Some ((Internal f)) =>
  let cenv := cenv_for f in
  let penv := build_penv cenv ((f.(fn_params) ++ f.(fn_vars))) 1%positive 1%positive  in
    PTree.get pos penv
    |_ => None
  end.

Definition unchecked_meminj : meminj :=
  fun b => match b with
    |Stack (Some id) path pos =>
      match find_func_pos id pos with
        | Some pos' => Some(Stack (Some id) path pos',0)
        | None => None
      end
    |_ => Some (b,0)
    end.

Definition struct_meminj (s:sup) : meminj :=
  fun b => if Mem.sup_dec b s then
           unchecked_meminj b else None.

Lemma sinj_refl:
  forall s1 s2, (forall b, sup_In b s1 <-> sup_In b s2) ->
           struct_meminj s1= struct_meminj s2.
Proof.
  intros.
  apply Axioms.extensionality.
  intros. destruct x; unfold struct_meminj; simpl.
  destruct (Mem.sup_dec (Stack f p p0) s1);
  destruct (Mem.sup_dec (Stack f p p0) s2).
  auto. apply H in s. congruence.
  apply H in s. congruence. auto.
  destr; destr. apply H in s. congruence.
  apply H in s. congruence.
Qed.

Lemma sinj_include_incr :forall s1 s2, Mem.sup_include s1 s2 -> inject_incr (struct_meminj s1) (struct_meminj s2).
Proof.
  intros. intro. intros. unfold struct_meminj in *.
  destruct b; simpl in *.
  destruct (Mem.sup_dec (Stack f p p0) s1);
  destruct (Mem.sup_dec (Stack f p p0) s2).
  auto. apply H in s. congruence. inv H0. inv H0.
  destr. destr_in H0. destr_in H0.
  inv H0. apply H in s. congruence.
Qed.

Inductive alloc_variables' (ge:genv): env -> mem -> list (ident * type) -> list block -> env -> mem -> Prop :=
  |av_nil : forall e m, alloc_variables' ge e m nil nil e m
  |av_cons : forall e m id ty vars m1 b1 m2 e2 blocks,
      Mem.alloc m 0 (sizeof ge ty) = (m1,b1) ->
      alloc_variables' ge (PTree.set id (b1,ty) e) m1 vars blocks e2 m2 ->
      alloc_variables' ge e m ((id,ty)::vars) (b1::blocks) e2 m2.


Lemma alloc_vars_fresh' : forall ge e1 m1 vars blocks e2 m2 b ,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    In b blocks -> ~ sup_In b (Mem.support m1).
Proof.
  intros. induction H. inv H0.
  inv H0. eapply Mem.fresh_block_alloc; eauto.
  intro. apply IHalloc_variables'. auto.
  eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma valid_block_alloc_vars' : forall ge e1 m1 vars blocks e2 m2 b,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    sup_In b (Mem.support m1) -> sup_In b (Mem.support m2).
Proof.
  intros. induction H. auto.
  eapply Mem.valid_block_alloc in H; eauto.
Qed.

Lemma alloc_vars_valid' : forall ge e1 m1 vars blocks e2 m2 b ,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    In b blocks -> sup_In b (Mem.support m2).
Proof.
  intros. induction H. inv H0.
  inv H0.
  eapply valid_block_alloc_vars' in H1; eauto.
  eapply Mem.valid_new_block; eauto.
  eauto.
Qed.

Lemma alloc_vars_inv'  : forall ge e1 m1 vars blocks e2 m2 b ,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    sup_In b (Mem.support m1) \/In b blocks <-> sup_In b (Mem.support m2).
Proof.
  intros. split. intros [A|B].
  eapply valid_block_alloc_vars'; eauto.
  eapply alloc_vars_valid'; eauto.
  intros. induction H. eauto.
  apply IHalloc_variables' in H0. inv H0.
  destruct (eq_block b b1). right. left. auto.
  left. exploit Mem.valid_block_alloc_inv; eauto.
  intros. inv H0. congruence. auto. right. right. auto.
Qed.

Lemma alloc_var_var' : forall ge e1 m1 vars e2 m2,
    alloc_variables ge e1 m1 vars e2 m2 ->
    exists blocks, alloc_variables' ge e1 m1 vars blocks e2 m2 /\
               list_norepet blocks.
Proof.
  intros. induction H.
  exists nil. split. constructor. constructor.
  destruct IHalloc_variables as (blocks & A & B).
  exists (b1::blocks). split. econstructor; eauto.
  constructor; auto. intro. apply alloc_vars_fresh' with (b:=b1)in A; auto.
  apply A. eapply Mem.valid_new_block; eauto.
Qed.

Lemma alloc_var'_var : forall ge e1 m1 vars blocks e2 m2,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    alloc_variables ge e1 m1 vars e2 m2.
Proof.
  intros. induction H. constructor.
  econstructor; eauto.
Qed.

End SINJ.

Definition nextblock_pos (m:mem) (p:positive) : Prop :=
  exists id path, Mem.nextblock m = Stack id path p.

Definition match_penv_meminj (b:block) (pe:posenv) (f:meminj) : Prop :=
  exists id path pos, b = Stack id path pos /\
                 (f b = match pe ! pos with
                          |Some pos' => Some ((Stack id path pos'),0)
                          |None => None
                 end ).

Lemma nextblock_pos_succ : forall m m1 lo hi p b,
    nextblock_pos m p ->
    Mem.alloc m lo hi = (m1,b) ->
    nextblock_pos m1 (Pos.succ p).
Proof.
  intros.
  caseEq (Mem.alloc m1 lo hi). intros.
  destruct H as (id & path & H). apply Mem.alloc_result in H0 as H0'. subst.
  exploit Mem.alloc_alloc. apply H0. apply H1. eauto. intro.
  exists id,path.
  apply Mem.alloc_result in H1 as H1'. subst. eauto.
Qed.

Lemma nextblock_pos_1 : forall m m1 id path,
    Mem.alloc_frame m id = (m1,path) ->
    nextblock_pos m1 1.
Proof.
  intros. caseEq (Mem.alloc m1 1 1). intros.
  exploit Mem.alloc_frame_alloc; eauto. intro.
  apply Mem.alloc_result in H0. exists (Some id),path. congruence.
Qed.

Lemma alloc_nextblock : forall m m1 lo hi b id path p,
    Mem.nextblock m = Stack id path p ->
    Mem.alloc m lo hi = (m1,b) ->
    Mem.nextblock m1 = Stack id path (Pos.succ p).
Proof.
  intros. caseEq (Mem.alloc m1 0 0). intros.
  exploit Mem.alloc_alloc. apply H0. eauto.
  apply Mem.alloc_result in H0. subst. eauto. intro.
  apply Mem.alloc_result in H1. congruence.
Qed.

Lemma nextblock_alloc_vars :
  forall m1 m2 ge e1 e2 vars blocks,
    alloc_variables' ge e1 m1 vars blocks e2 m2 ->
    forall id path p,
    Mem.nextblock m1 = Stack id path p ->
    (forall b, In b blocks ->
          exists p', b = Stack id path p' /\ (p <= p')%positive).
Proof.
  induction 1.
  intros. inv H0.
  intros. inv H2.
  - apply Mem.alloc_result in H. subst. rewrite H1.
    exists p. split. auto. lia.
  - exploit alloc_nextblock; eauto. intro.
    eapply IHalloc_variables' in H2. destruct H2 as (p' & A & B).
    exists p'. split. eauto. lia. auto.
Qed.

Lemma match_alloc_variables':
  forall cenv e m vars blocks e' m',
  alloc_variables' ge e m vars blocks e' m' ->
  forall j tm te pe idx1 idx2,
  list_norepet (var_names vars) ->
  Mem.inject j m tm ->
  Mem.stackseq m tm ->
  pe = build_penv cenv vars idx1 idx2 ->
  nextblock_pos m idx1 ->
  nextblock_pos tm idx2 ->
  exists j', exists te', exists tm',
      alloc_variables tge te tm (remove_lifted cenv vars) te' tm'
  /\ Mem.inject j' m' tm'
  /\ inject_incr j j'
  /\ (forall b, Mem.valid_block m b -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> ~Mem.valid_block tm b' ->
         exists id, exists ty, e'!id = Some(b, ty) /\ te'!id = Some(b', ty) /\ delta = 0)
  /\ (forall id ty, In (id, ty) vars ->
      exists b,
          e'!id = Some(b, ty)
       /\ if VSet.mem id cenv
          then te'!id = te!id /\ j' b = None
          else exists tb, te'!id = Some(tb, ty) /\ j' b = Some(tb, 0))
  /\ (forall id, ~In id (var_names vars) -> e'!id = e!id /\ te'!id = te!id)
  /\ (forall b, In b blocks -> match_penv_meminj b pe j').
Proof.
  induction 1; intros.
  (* base case *)
  exists j; exists te; exists tm. simpl.
  split. constructor.
  split. auto. split. auto. split. auto.  split. auto.
  split. intros. elim H6. eapply Mem.mi_mappedblocks; eauto.
  split. tauto. tauto.

  (* inductive case *)
  simpl in H1. inv H1. simpl.
  destruct (VSet.mem id cenv) eqn:?.
  - simpl.
  (* variable is lifted out of memory *)
  exploit Mem.alloc_left_unmapped_inject; eauto.
  intros [j1 [A [B [C D]]]].
  exploit IHalloc_variables'; eauto.
  eapply struct_eq_trans. 2:eauto.
  eapply struct_eq_comm. eapply Mem.alloc_stackseq; eauto.
  eapply nextblock_pos_succ. apply H5. eauto.
  instantiate (1 := te).
  intros [j' [te' [tm' [J [K [L [M [N [Q [O [P R]]]]]]]]]]].
  exists j'; exists te'; exists tm'.
  split. auto.
  split. auto.
  split. eapply inject_incr_trans; eauto.
  split. intros. transitivity (j1 b). apply M. eapply Mem.valid_block_alloc; eauto.
    apply D. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto.
  split. intros. transitivity (j1 b). eapply N; eauto.
    destruct (eq_block b b1); auto. subst.
    assert (j' b1 = j1 b1). apply M. eapply Mem.valid_new_block; eauto.
    congruence.
  split. exact Q.
  split. intros. destruct (ident_eq id0 id).
    (* same var *)
    subst id0.
    assert (ty0 = ty).
      destruct H1. congruence. elim H9. unfold var_names. change id with (fst (id, ty0)). apply in_map; auto.
    subst ty0.
    exploit P; eauto. intros [X Y]. rewrite Heqb. rewrite X. rewrite Y.
    exists b1. split. apply PTree.gss.
    split. auto.
    rewrite M. auto. eapply Mem.valid_new_block; eauto.
    (* other vars *)
    eapply O; eauto. destruct H1. congruence. auto.
  split. intros. exploit (P id0). tauto. intros [X Y]. rewrite X; rewrite Y.
    split; auto. apply PTree.gso. intuition.
  intros. inv H1. unfold match_penv_meminj.
  exploit Mem.alloc_result; eauto. intro.
  destruct H5 as (fid & path & H5). rewrite H5 in H1.
  exists fid,path,idx1. split. congruence.
  rewrite M. rewrite C. rewrite build_penv_low. auto. lia.
  eapply Mem.valid_new_block. eauto.
  eauto.
-
  (* variable is not lifted out of memory *)
  exploit Mem.alloc_parallel_inject.
    eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [j1 [tm1 [tb1 [A [B [C [D E]]]]]]].
  exploit IHalloc_variables'; eauto.
  eapply struct_eq_trans. eapply struct_eq_comm.
  eapply Mem.alloc_stackseq; eauto.
  eapply struct_eq_trans; eauto. eapply Mem.alloc_stackseq; eauto.
  eapply nextblock_pos_succ. apply H5. eauto.
  eapply nextblock_pos_succ. apply H6. eauto.
  instantiate (1 := PTree.set id (tb1, ty) te).
  intros [j' [te' [tm' [J [K [L [M [N [Q [O [P R]]]]]]]]]]].
  exists j'; exists te'; exists tm'.
  split. simpl. econstructor; eauto. rewrite comp_env_preserved; auto.
  split. auto.
  split. eapply inject_incr_trans; eauto.
  split. intros. transitivity (j1 b). apply M. eapply Mem.valid_block_alloc; eauto.
    apply E. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto.
  split. intros. transitivity (j1 b). eapply N; eauto. eapply Mem.valid_block_alloc; eauto.
    destruct (eq_block b b1); auto. subst.
    assert (j' b1 = j1 b1). apply M. eapply Mem.valid_new_block; eauto.
    rewrite H7 in H1. rewrite D in H1. inv H1. eelim Mem.fresh_block_alloc; eauto.
  split. intros. destruct (eq_block b' tb1).
    subst b'. rewrite (N _ _ _ H1) in H1.
    destruct (eq_block b b1). subst b. rewrite D in H1; inv H1.
    exploit (P id); auto. intros [X Y]. exists id; exists ty.
    rewrite X; rewrite Y. repeat rewrite PTree.gss. auto.
    rewrite E in H1; auto. elim H4. eapply Mem.mi_mappedblocks; eauto.
    eapply Mem.valid_new_block; eauto.
    eapply Q; eauto. unfold Mem.valid_block in *.
    intro. eapply Mem.valid_block_alloc_inv in H7. destruct H7. eauto.
    eauto. eauto.
  split. intros. destruct (ident_eq id0 id).
    (* same var *)
    subst id0.
    assert (ty0 = ty).
      destruct H1. congruence. elim H9. unfold var_names. change id with (fst (id, ty0)). apply in_map; auto.
    subst ty0.
    exploit P; eauto. intros [X Y]. rewrite Heqb. rewrite X. rewrite Y.
    exists b1. split. apply PTree.gss.
    exists tb1; split.
    apply PTree.gss.
    rewrite M. auto. eapply Mem.valid_new_block; eauto.
    (* other vars *)
    exploit (O id0 ty0). destruct H1. congruence. auto.
    rewrite PTree.gso; auto.
  split. intros. exploit (P id0). tauto. intros [X Y]. rewrite X; rewrite Y.
    split; apply PTree.gso; intuition.
  intros. inv H1. unfold match_penv_meminj.
  exploit Mem.alloc_result. apply H. intro.
  exploit Mem.alloc_result. apply A. intro.
  destruct H5 as (id0 & path0 & H5).
  destruct H6 as (id1 & path1 & H6).
  exploit Mem.stackseq_id_path; eauto. intros. inv H7.
  exists id1 ,path1,idx1. split. congruence.
  rewrite PTree.gss. rewrite M. rewrite D. rewrite H6. auto.
  eapply Mem.valid_new_block. eauto.
  exploit R; eauto. intros. unfold match_penv_meminj in H1.
  destruct H1 as (id1 & path1 & pos1 & X & Y).
  unfold match_penv_meminj. exists id1,path1,pos1. split. auto.
  rewrite PTree.gso. eauto.
  exploit nextblock_pos_succ. apply H5. eauto. intro.
  assert (pos1 >= Pos.succ idx1)%positive.
  destruct H1 as (id0 &path0 & H1).
  exploit nextblock_alloc_vars; eauto. intros (p' & X' & Y').
  rewrite X in X'. inv X'. lia. lia.
Qed.

Lemma alloc_variables_load:
  forall e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  forall chunk b ofs v,
  Mem.load chunk m b ofs = Some v ->
  Mem.load chunk m' b ofs = Some v.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. eapply Mem.load_alloc_other; eauto.
Qed.

Lemma sizeof_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk -> size_chunk chunk <= sizeof ge ty.
Proof.
  unfold access_mode; intros.
  assert (size_chunk chunk = sizeof ge ty).
  {
    destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; auto.
  }
  lia.
Qed.

Definition env_initial_value (e: env) (m: mem) :=
  forall id b ty chunk,
  e!id = Some(b, ty) -> access_mode ty = By_value chunk -> Mem.load chunk m b 0 = Some Vundef.

Lemma alloc_variables_initial_value:
  forall e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  env_initial_value e m ->
  env_initial_value e' m'.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. red; intros. rewrite PTree.gsspec in H2.
  destruct (peq id0 id). inv H2.
  eapply Mem.load_alloc_same'; eauto.
  lia. rewrite Z.add_0_l. eapply sizeof_by_value; eauto.
  apply Z.divide_0_r.
  eapply Mem.load_alloc_other; eauto.
Qed.

Lemma create_undef_temps_charact:
  forall id ty vars, In (id, ty) vars -> (create_undef_temps vars)!id = Some Vundef.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss.
  destruct a as [id1 ty1]. rewrite PTree.gsspec. destruct (peq id id1); auto.
Qed.

Lemma create_undef_temps_inv:
  forall vars id v, (create_undef_temps vars)!id = Some v -> v = Vundef /\ In id (var_names vars).
Proof.
  induction vars; simpl; intros.
  rewrite PTree.gempty in H; congruence.
  destruct a as [id1 ty1]. rewrite PTree.gsspec in H. destruct (peq id id1).
  inv H. auto.
  exploit IHvars; eauto. tauto.
Qed.

Lemma create_undef_temps_exten:
  forall id l1 l2,
  (In id (var_names l1) <-> In id (var_names l2)) ->
  (create_undef_temps l1)!id = (create_undef_temps l2)!id.
Proof.
  assert (forall id l1 l2,
          (In id (var_names l1) -> In id (var_names l2)) ->
          (create_undef_temps l1)!id = None \/ (create_undef_temps l1)!id = (create_undef_temps l2)!id).
    intros. destruct ((create_undef_temps l1)!id) as [v1|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [A B]. subst v1.
    exploit list_in_map_inv. unfold var_names in H. apply H. eexact B.
    intros [[id1 ty1] [P Q]]. simpl in P; subst id1.
    right; symmetry; eapply create_undef_temps_charact; eauto.
  intros.
  exploit (H id l1 l2). tauto.
  exploit (H id l2 l1). tauto.
  intuition congruence.
Qed.

Remark var_names_app:
  forall vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2.
Proof.
  intros. apply map_app.
Qed.

Remark filter_app:
  forall (A: Type) (f: A -> bool) l1 l2,
  List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof.
  induction l1; simpl; intros.
  auto.
  destruct (f a). simpl. decEq; auto. auto.
Qed.

Remark filter_charact:
  forall (A: Type) (f: A -> bool) x l,
  In x (List.filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; simpl. tauto.
  destruct (f a) eqn:?.
  simpl. rewrite IHl. intuition congruence.
  intuition congruence.
Qed.

Remark filter_norepet:
  forall (A: Type) (f: A -> bool) l,
  list_norepet l -> list_norepet (List.filter f l).
Proof.
  induction 1; simpl. constructor.
  destruct (f hd); auto. constructor; auto. rewrite filter_charact. tauto.
Qed.

Remark filter_map:
  forall (A B: Type) (f: A -> B) (pa: A -> bool) (pb: B -> bool),
  (forall a, pb (f a) = pa a) ->
  forall l, List.map f (List.filter pa l) = List.filter pb (List.map f l).
Proof.
  induction l; simpl.
  auto.
  rewrite H. destruct (pa a); simpl; congruence.
Qed.

Lemma create_undef_temps_lifted:
  forall id f,
  ~ In id (var_names (fn_params f)) ->
  (create_undef_temps (add_lifted (cenv_for f) (fn_vars f) (fn_temps f))) ! id =
  (create_undef_temps (add_lifted (cenv_for f) (fn_params f ++ fn_vars f) (fn_temps f))) ! id.
Proof.
  intros. apply create_undef_temps_exten.
  unfold add_lifted. rewrite filter_app.
  unfold var_names in *.
  repeat rewrite map_app. repeat rewrite in_app. intuition.
  exploit list_in_map_inv; eauto. intros [[id1 ty1] [P Q]]. simpl in P. subst id.
  rewrite filter_charact in Q. destruct Q.
  elim H. change id1 with (fst (id1, ty1)). apply List.in_map. auto.
Qed.

Lemma vars_and_temps_properties:
  forall cenv params vars temps,
  list_norepet (var_names params ++ var_names vars) ->
  list_disjoint (var_names params) (var_names temps) ->
  list_norepet (var_names params)
  /\ list_norepet (var_names (remove_lifted cenv (params ++ vars)))
  /\ list_disjoint (var_names params) (var_names (add_lifted cenv vars temps)).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]].
  split. auto.
  split. unfold remove_lifted. unfold var_names. erewrite filter_map.
  instantiate (1 := fun a => negb (VSet.mem a cenv)). 2: auto.
  apply filter_norepet. rewrite map_app. apply list_norepet_append; assumption.
  unfold add_lifted. rewrite var_names_app.
  unfold var_names at 2. erewrite filter_map.
  instantiate (1 := fun a => VSet.mem a cenv). 2: auto.
  change (map fst vars) with (var_names vars).
  red; intros.
  rewrite in_app in H1. destruct H1.
  rewrite filter_charact in H1. destruct H1. apply C; auto.
  apply H0; auto.
Qed.

Theorem match_envs_alloc_variables:
  forall cenv m vars e m' temps j tm blocks pe idx1 idx2,
  alloc_variables' ge empty_env m vars blocks e m' ->
  list_norepet (var_names vars) ->
  Mem.inject j m tm ->
  Mem.stackseq m tm ->
  pe = build_penv cenv vars idx1 idx2 ->
  nextblock_pos m idx1 ->
  nextblock_pos tm idx2 ->
  (forall id ty, In (id, ty) vars -> VSet.mem id cenv = true ->
                     exists chunk, access_mode ty = By_value chunk) ->
  (forall id, VSet.mem id cenv = true -> In id (var_names vars)) ->
  exists j', exists te, exists tm',
     alloc_variables tge empty_env tm (remove_lifted cenv vars) te tm'
  /\ match_envs j' cenv e (create_undef_temps temps) m' (Mem.support m) (Mem.support m')
                        te (create_undef_temps (add_lifted cenv vars temps)) (Mem.support tm) (Mem.support tm')
  /\ Mem.inject j' m' tm'
  /\ inject_incr j j'
  /\ (forall b, Mem.valid_block m b -> j' b = j b)
  /\ (forall b b' delta, j' b = Some(b', delta) -> Mem.valid_block tm b' -> j' b = j b)
  /\ (forall id ty, In (id, ty) vars -> VSet.mem id cenv = false -> exists b, te!id = Some(b, ty))
  /\ (forall b, In b blocks -> match_penv_meminj b pe j').
Proof.
  intros.
  exploit (match_alloc_variables' cenv); eauto. instantiate (1 := empty_env).
  intros [j' [te [tm' [A [B [C [D [E [K [F [G I]]]]]]]]]]].
  exists j'; exists te; exists tm'.
  split. auto. split; auto.
  constructor; intros.
  (* vars *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto.
  intros [[id' ty] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P R]].
  destruct (VSet.mem id cenv) eqn:?.
  (* local var, lifted *)
  destruct R as [U V]. exploit H6; eauto. intros [chunk X].
  eapply match_var_lifted with (v := Vundef) (tv := Vundef); eauto.
  rewrite U; apply PTree.gempty.
  eapply alloc_variables_initial_value; eauto.
  eapply alloc_var'_var; eauto.
   red. unfold empty_env; intros. rewrite PTree.gempty in H8; congruence.
  apply create_undef_temps_charact with ty.
  unfold add_lifted. apply in_or_app. left.
  rewrite filter_In. auto.
  (* local var, not lifted *)
  destruct R as [tb [U V]].
  eapply match_var_not_lifted; eauto.
  (* non-local var *)
  exploit G; eauto. unfold empty_env. rewrite PTree.gempty. intros [U V].
  eapply match_var_not_local; eauto.
  destruct (VSet.mem id cenv) eqn:?; auto.
  elim n; eauto.

  (* temps *)
  exploit create_undef_temps_inv; eauto. intros [P Q]. subst v.
  unfold var_names in Q. exploit list_in_map_inv; eauto.
  intros [[id1 ty] [EQ IN]]; simpl in EQ; subst id1.
  split; auto. exists Vundef; split; auto.
  apply create_undef_temps_charact with ty. unfold add_lifted.
  apply in_or_app; auto.

  (* injective *)
  eapply alloc_variables_injective.
  eapply alloc_var'_var; eauto.
  rewrite PTree.gempty. congruence.
  intros. rewrite PTree.gempty in H11. congruence.
  eauto. eauto. auto.

  (* range *)
  exploit alloc_variables_range. eapply alloc_var'_var. eexact H. eauto.
  rewrite PTree.gempty. intuition congruence.

  (* trange *)
  exploit alloc_variables_range. eexact A. eauto.
  rewrite PTree.gempty. intuition congruence.

  (* mapped *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto.
  intros [[id' ty'] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P Q]].
  destruct (VSet.mem id cenv).
  rewrite PTree.gempty in Q. destruct Q; congruence.
  destruct Q as [tb [U V]]. exists b; split; congruence.
  exploit G; eauto. rewrite PTree.gempty. intuition congruence.

  (* flat *)
  exploit alloc_variables_range. eexact A. eauto.
  rewrite PTree.gempty. intros [P|P]. congruence.
  exploit K; eauto. unfold Mem.valid_block. destruct P. auto.
  intros [id0 [ty0 [U [V W]]]]. split; auto.
  destruct (ident_eq id id0). congruence.
  assert (b' <> b').
  eapply alloc_variables_injective with (e' := te) (id1 := id) (id2 := id0); eauto.
  rewrite PTree.gempty; congruence.
  intros until ty1; rewrite PTree.gempty; congruence.
  congruence.

  (* incr *)
  eapply alloc_variables_support; eapply alloc_var'_var; eauto.
  eapply alloc_variables_support; eauto.

  (* other properties *)
  intuition auto. edestruct F as (b & X & Y); eauto. rewrite H9 in Y.
  destruct Y as (tb & U & V). exists tb; auto.
Qed.

Lemma assign_loc_inject:
  forall f ty m loc ofs v m' tm loc' ofs' v',
  assign_loc ge ty m loc ofs v m' ->
  Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  Val.inject f v v' ->
  Mem.inject f m tm ->
  exists tm',
     assign_loc tge ty tm loc' ofs' v' tm'
  /\ Mem.inject f m' tm'
  /\ (forall b chunk v,
      f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv H.
- (* by value *)
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto.
  split. auto.
  intros. rewrite <- H5. eapply Mem.load_store_other; eauto.
  left. inv H0. congruence.
- (* by copy *)
  inv H0. inv H1.
  rename b' into bsrc. rename ofs'0 into osrc.
  rename loc into bdst. rename ofs into odst.
  rename loc' into bdst'. rename b2 into bsrc'.
  rewrite <- comp_env_preserved in *.
  destruct (zeq (sizeof tge ty) 0).
+ (* special case size = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m bsrc (Ptrofs.unsigned osrc) (sizeof tge ty)).
    lia. congruence. }
  subst.
  destruct (Mem.range_perm_storebytes tm bdst' (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta))) nil)
  as [tm' SB].
  simpl. red; intros; extlia.
  exists tm'.
  split. eapply assign_loc_copy; eauto.
  intros; extlia.
  intros; extlia.
  rewrite e; right; lia.
  apply Mem.loadbytes_empty. lia.
  split. eapply Mem.storebytes_empty_inject; eauto.
  intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto.
  left. congruence.
+ (* general case size > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (SZPOS: sizeof tge ty > 0).
  { generalize (sizeof_pos tge ty); lia. }
  assert (RPSRC: Mem.range_perm m bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sizeof tge ty) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sizeof tge ty) Cur Nonempty).
    replace (sizeof tge ty) with (Z.of_nat (List.length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia.
  assert (PSRC: Mem.perm m bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
  assert (PDST: Mem.perm m bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. lia.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'.
  split. eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m); eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_alignof_blockcopy_compat.
  intros; eapply Mem.aligned_area_inject with (m := m); eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_alignof_blockcopy_compat.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. auto.
  intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto.
  left. congruence.
Qed.

Lemma assign_loc_support:
  forall ge ty m b ofs v m',
  assign_loc ge ty m b ofs v m' -> Mem.support m' = Mem.support m.
Proof.
  induction 1.
  simpl in H0. eapply Mem.support_store; eauto.
  eapply Mem.support_storebytes; eauto.
Qed.

Theorem store_params_correct:
  forall j f k cenv le lo hi te tlo thi e m params args m',
  bind_parameters ge e m params args m' ->
  forall s tm tle1 tle2 targs,
  list_norepet (var_names params) ->
  list_forall2 val_casted args (map snd params) ->
  Val.inject_list j args targs ->
  match_envs j cenv e le m lo hi te tle1 tlo thi ->
  Mem.inject j m tm ->
  (forall id, ~In id (var_names params) -> tle2!id = tle1!id) ->
  (forall id, In id (var_names params) -> le!id = None) ->
  exists tle, exists tm',
  star step2 tge (State f (store_params cenv params s) k te tle tm)
              E0 (State f s k te tle tm')
  /\ bind_parameter_temps params targs tle2 = Some tle
  /\ Mem.inject j m' tm'
  /\ match_envs j cenv e le m' lo hi te tle tlo thi
  /\ Mem.support tm' = Mem.support tm.
Proof.
  induction 1; simpl; intros until targs; intros NOREPET CASTED VINJ MENV MINJ TLE LE.
  (* base case *)
  inv VINJ. exists tle2; exists tm; split. apply star_refl. split. auto. split. auto.
  split. apply match_envs_temps_exten with tle1; auto. auto.
  (* inductive case *)
  inv NOREPET. inv CASTED. inv VINJ.
  exploit me_vars; eauto. instantiate (1 := id); intros MV.
  destruct (VSet.mem id cenv) eqn:?.
  (* lifted to temp *)
  eapply IHbind_parameters with (tle1 := PTree.set id v' tle1); eauto.
  eapply match_envs_assign_lifted; eauto.
  inv MV; try congruence. rewrite ENV in H; inv H.
  inv H0; try congruence.
  unfold Mem.storev in H2. eapply Mem.store_unmapped_inject; eauto.
  intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
  apply TLE. intuition.
  (* still in memory *)
  inv MV; try congruence. rewrite ENV in H; inv H.
  exploit assign_loc_inject; eauto.
  intros [tm1 [A [B C]]].
  exploit IHbind_parameters. eauto. eauto. eauto.
  instantiate (1 := PTree.set id v' tle1).
  apply match_envs_change_temp.
  eapply match_envs_invariant; eauto.
  apply LE; auto. auto.
  eauto.
  instantiate (1 := PTree.set id v' tle2).
  intros. repeat rewrite PTree.gsspec. destruct (peq id0 id). auto.
  apply TLE. intuition.
  intros. apply LE. auto.
  instantiate (1 := s).
  intros [tle [tm' [U [V [X [Y Z]]]]]].
  exists tle; exists tm'; split.
  eapply star_trans.
  eapply star_left. econstructor.
  eapply star_left. econstructor.
    eapply eval_Evar_local. eauto.
    eapply eval_Etempvar. erewrite bind_parameter_temps_inv; eauto.
    apply PTree.gss.
    simpl. instantiate (1 := v'). apply cast_val_casted.
    eapply val_casted_inject with (v := v1); eauto.
    simpl. eexact A.
  apply star_one. constructor.
  reflexivity. reflexivity.
  eexact U.
  traceEq.
  rewrite (assign_loc_support _ _ _ _ _ _ _ A) in Z. auto.
Qed.

Lemma bind_parameters_support:
  forall ge e m params args m',
  bind_parameters ge e m params args m' -> Mem.support m' = Mem.support m.
Proof.
  induction 1.
  auto.
  rewrite IHbind_parameters. eapply assign_loc_support; eauto.
Qed.

Lemma bind_parameters_load:
  forall ge e chunk b ofs,
  (forall id b' ty, e!id = Some(b', ty) -> b <> b') ->
  forall m params args m',
  bind_parameters ge e m params args m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2.
  auto.
  rewrite IHbind_parameters.
  assert (b <> b0) by eauto.
  inv H1.
  simpl in H5. eapply Mem.load_store_other; eauto.
  eapply Mem.load_storebytes_other; eauto.
Qed.

(** Freeing of local variables *)

Lemma free_blocks_of_env_perm_1:
  forall ce m e m' id b ty ofs k p,
  Mem.free_list m (blocks_of_env ce e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.perm m' b ofs k p ->
  0 <= ofs < sizeof ce ty ->
  False.
Proof.
  intros. exploit Mem.perm_free_list; eauto. intros [A B].
  apply B with 0 (sizeof ce ty); auto.
  unfold blocks_of_env. change (b, 0, sizeof ce ty) with (block_of_binding ce (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma free_list_perm':
  forall b lo hi l m m',
  Mem.free_list m l = Some m' ->
  In (b, lo, hi) l ->
  Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a as [[b1 lo1] hi1].
  destruct (Mem.free m b1 lo1 hi1) as [m1|] eqn:?; try discriminate.
  destruct H0. inv H0. eapply Mem.free_range_perm; eauto.
  red; intros. eapply Mem.perm_free_3; eauto. eapply IHl; eauto.
Qed.

Lemma free_blocks_of_env_perm_2:
  forall ce m e m' id b ty,
  Mem.free_list m (blocks_of_env ce e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.range_perm m b 0 (sizeof ce ty) Cur Freeable.
Proof.
  intros. eapply free_list_perm'; eauto.
  unfold blocks_of_env. change (b, 0, sizeof ce ty) with (block_of_binding ce (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Fixpoint freelist_no_overlap (l: list (block * Z * Z)) : Prop :=
  match l with
  | nil => True
  | (b, lo, hi) :: l' =>
      freelist_no_overlap l' /\
      (forall b' lo' hi', In (b', lo', hi') l' ->
       b' <> b \/ hi' <= lo \/ hi <= lo')
  end.

Lemma can_free_list:
  forall l m,
  (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
  freelist_no_overlap l ->
  exists m', Mem.free_list m l = Some m'.
Proof.
  induction l; simpl; intros.
- exists m; auto.
- destruct a as [[b lo] hi]. destruct H0.
  destruct (Mem.range_perm_free m b lo hi) as [m1 A]; auto.
  rewrite A. apply IHl; auto.
  intros. red; intros. eapply Mem.perm_free_1; eauto.
  exploit H1; eauto. intros [B|B]. auto. right; lia.
  eapply H; eauto.
Qed.

Lemma blocks_of_env_no_overlap:
  forall (ge: genv) j cenv e le m lo hi te tle tlo thi tm,
  match_envs j cenv e le m lo hi te tle tlo thi ->
  Mem.inject j m tm ->
  (forall id b ty,
   e!id = Some(b, ty) -> Mem.range_perm m b 0 (sizeof ge ty) Cur Freeable) ->
  forall l,
  list_norepet (List.map fst l) ->
  (forall id bty, In (id, bty) l -> te!id = Some bty) ->
  freelist_no_overlap (List.map (block_of_binding ge) l).
Proof.
  intros until tm; intros ME MINJ PERMS. induction l; simpl; intros.
- auto.
- destruct a as [id [b ty]]. simpl in *. inv H. split.
  + apply IHl; auto.
  + intros. exploit list_in_map_inv; eauto. intros [[id' [b'' ty']] [A B]].
    simpl in A. inv A. rename b'' into b'.
    assert (TE: te!id = Some(b, ty)) by eauto.
    assert (TE': te!id' = Some(b', ty')) by eauto.
    exploit me_mapped. eauto. eexact TE. intros [b0 [INJ E]].
    exploit me_mapped. eauto. eexact TE'. intros [b0' [INJ' E']].
    destruct (zle (sizeof ge0 ty) 0); auto.
    destruct (zle (sizeof ge0 ty') 0); auto.
    assert (b0 <> b0').
    { eapply me_inj; eauto. red; intros; subst; elim H3.
      change id' with (fst (id', (b', ty'))). apply List.in_map; auto. }
    assert (Mem.perm m b0 0 Max Nonempty).
    { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable.
      eapply PERMS; eauto. lia. auto with mem. }
    assert (Mem.perm m b0' 0 Max Nonempty).
    { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable.
      eapply PERMS; eauto. lia. auto with mem. }
    exploit Mem.mi_no_overlap; eauto. intros [A|A]. auto. extlia.
Qed.

Lemma free_list_right_inject:
  forall j m1 l m2 m2',
  Mem.inject j m1 m2 ->
  Mem.free_list m2 l = Some m2' ->
  (forall b1 b2 delta lo hi ofs k p,
     j b1 = Some(b2, delta) -> In (b2, lo, hi) l ->
     Mem.perm m1 b1 ofs k p -> lo <= ofs + delta < hi -> False) ->
  Mem.inject j m1 m2'.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a as [[b lo] hi]. destruct (Mem.free m2 b lo hi) as [m21|] eqn:?; try discriminate.
  eapply IHl with (m2 := m21); eauto.
  eapply Mem.free_right_inject; eauto.
Qed.

Lemma blocks_of_env_translated:
  forall e, blocks_of_env tge e = blocks_of_env ge e.
Proof.
  intros. unfold blocks_of_env, block_of_binding.
  rewrite comp_env_preserved; auto.
Qed.

Theorem match_envs_free_blocks:
  forall j cenv e le m lo hi te tle tlo thi m' tm,
  match_envs j cenv e le m lo hi te tle tlo thi ->
  Mem.inject j m tm ->
  Mem.free_list m (blocks_of_env ge e) = Some m' ->
  exists tm',
     Mem.free_list tm (blocks_of_env tge te) = Some tm'
  /\ Mem.inject j m' tm'.
Proof.
  intros.
Local Opaque ge tge.
  assert (X: exists tm', Mem.free_list tm (blocks_of_env tge te) = Some tm').
  {
    rewrite blocks_of_env_translated. apply can_free_list.
  - (* permissions *)
    intros. unfold blocks_of_env in H2.
    exploit list_in_map_inv; eauto. intros [[id [b' ty]] [EQ IN]].
    unfold block_of_binding in EQ; inv EQ.
    exploit me_mapped; eauto. eapply PTree.elements_complete; eauto.
    intros [b [A B]].
    change 0 with (0 + 0). replace (sizeof ge ty) with (sizeof ge ty + 0) by lia.
    eapply Mem.range_perm_inject; eauto.
    eapply free_blocks_of_env_perm_2; eauto.
  - (* no overlap *)
    unfold blocks_of_env; eapply blocks_of_env_no_overlap; eauto.
    intros. eapply free_blocks_of_env_perm_2; eauto.
    apply PTree.elements_keys_norepet.
    intros. apply PTree.elements_complete; auto.
  }
  destruct X as [tm' FREE].
  exists tm'; split; auto.
  eapply free_list_right_inject; eauto.
  eapply Mem.free_list_left_inject; eauto.
  intros. unfold blocks_of_env in H3. exploit list_in_map_inv; eauto.
  intros [[id [b' ty]] [EQ IN]]. unfold block_of_binding in EQ. inv EQ.
  exploit me_flat; eauto. apply PTree.elements_complete; eauto.
  intros [P Q]. subst delta. eapply free_blocks_of_env_perm_1 with (m := m); eauto.
  rewrite <- comp_env_preserved. lia.
Qed.

(** Matching global environments *)

Inductive match_globalenvs (f: meminj) (bound: sup): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, sup_In b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> sup_In b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> sup_In b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> sup_In b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> sup_In b bound).

Lemma match_globalenvs_preserves_globals:
  forall f,
  (exists bound, match_globalenvs f bound) ->
  meminj_preserves_globals ge f.
Proof.
  intros. destruct H as [bound MG]. inv MG.
  split; intros. eauto. split; intros. eauto. symmetry. eapply IMAGE; eauto.
Qed.

(** Evaluation of expressions *)

Section EVAL_EXPR.

Variables e te: env.
Variables le tle: temp_env.
Variables m tm: mem.
Variable f: meminj.
Variable cenv: compilenv.
Variables lo hi tlo thi: sup.
Hypothesis MATCH: match_envs f cenv e le m lo hi te tle tlo thi.
Hypothesis MEMINJ: Mem.inject f m tm.
Hypothesis GLOB: exists bound, match_globalenvs f bound.

Lemma typeof_simpl_expr:
  forall a, typeof (simpl_expr cenv a) = typeof a.
Proof.
  destruct a; simpl; auto. destruct (VSet.mem i cenv); auto.
Qed.

Lemma deref_loc_inject:
  forall ty loc ofs v loc' ofs',
  deref_loc ty m loc ofs v ->
  Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  exists tv, deref_loc ty tm loc' ofs' tv /\ Val.inject f v tv.
Proof.
  intros. inv H.
  (* by value *)
  exploit Mem.loadv_inject; eauto. intros [tv [A B]].
  exists tv; split; auto. eapply deref_loc_value; eauto.
  (* by reference *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_reference; eauto.
  (* by copy *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_copy; eauto.
Qed.

Lemma eval_simpl_expr:
  forall a v,
  eval_expr ge e le m a v ->
  compat_cenv (addr_taken_expr a) cenv ->
  exists tv, eval_expr tge te tle tm (simpl_expr cenv a) tv /\ Val.inject f v tv

with eval_simpl_lvalue:
  forall a b ofs,
  eval_lvalue ge e le m a b ofs ->
  compat_cenv (addr_taken_expr a) cenv ->
  match a with Evar id ty => VSet.mem id cenv = false | _ => True end ->
  exists b', exists ofs', eval_lvalue tge te tle tm (simpl_expr cenv a) b' ofs' /\ Val.inject f (Vptr b ofs) (Vptr b' ofs').

Proof.
  destruct 1; simpl; intros.
(* const *)
  exists (Vint i); split; auto. constructor.
  exists (Vfloat f0); split; auto. constructor.
  exists (Vsingle f0); split; auto. constructor.
  exists (Vlong i); split; auto. constructor.
(* tempvar *)
  exploit me_temps; eauto. intros [[tv [A B]] C].
  exists tv; split; auto. constructor; auto.
(* addrof *)
  exploit eval_simpl_lvalue; eauto.
  destruct a; auto with compat.
  destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto.
  elim (H0 i). apply VSet.singleton_2. auto. apply VSet.mem_2. auto.
  intros [b' [ofs' [A B]]].
  exists (Vptr b' ofs'); split; auto. constructor; auto.
(* unop *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_unary_operation_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor; eauto. rewrite typeof_simpl_expr; auto.
(* binop *)
  exploit eval_simpl_expr. eexact H. eauto with compat. intros [tv1 [A B]].
  exploit eval_simpl_expr. eexact H0. eauto with compat. intros [tv2 [C D]].
  exploit sem_binary_operation_inject; eauto. intros [tv [E F]].
  exists tv; split; auto. econstructor; eauto.
  repeat rewrite typeof_simpl_expr; rewrite comp_env_preserved; auto.
(* cast *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]].
  exists tv2; split; auto. econstructor. eauto. rewrite typeof_simpl_expr; auto.
(* sizeof *)
  econstructor; split. constructor. rewrite comp_env_preserved; auto.
(* alignof *)
  econstructor; split. constructor. rewrite comp_env_preserved; auto.
(* rval *)
  assert (EITHER: (exists id, exists ty, a = Evar id ty /\ VSet.mem id cenv = true)
               \/ (match a with Evar id _ => VSet.mem id cenv = false | _ => True end)).
    destruct a; auto. destruct (VSet.mem i cenv) eqn:?; auto. left; exists i; exists t; auto.
  destruct EITHER as [ [id [ty [EQ OPT]]] | NONOPT ].
  (* a variable pulled out of memory *)
  subst a. simpl. rewrite OPT.
  exploit me_vars; eauto. instantiate (1 := id). intros MV.
  inv H; inv MV; try congruence.
  rewrite ENV in H6; inv H6.
  inv H0; try congruence.
  assert (chunk0 = chunk). simpl in H. congruence. subst chunk0.
  assert (v0 = v). unfold Mem.loadv in H2. rewrite Ptrofs.unsigned_zero in H2. congruence. subst v0.
  exists tv; split; auto. constructor; auto.
  simpl in H; congruence.
  simpl in H; congruence.
  (* any other l-value *)
  exploit eval_simpl_lvalue; eauto. intros [loc' [ofs' [A B]]].
  exploit deref_loc_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor. eexact A. rewrite typeof_simpl_expr; auto.

(* lvalues *)
  destruct 1; simpl; intros.
(* local var *)
  rewrite H1.
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  rewrite ENV in H; inv H.
  exists b'; exists Ptrofs.zero; split.
  apply eval_Evar_local; auto.
  econstructor; eauto.
(* global var *)
  rewrite H2.
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  exists l; exists Ptrofs.zero; split.
  apply eval_Evar_global. auto. rewrite <- H0. apply symbols_preserved.
  destruct GLOB as [bound GLOB1]. inv GLOB1.
  econstructor; eauto.
(* deref *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]].
  inversion B. subst.
  econstructor; econstructor; split; eauto. econstructor; eauto.
(* field struct *)
  rewrite <- comp_env_preserved in *.
  exploit eval_simpl_expr; eauto. intros [tv [A B]].
  inversion B. subst.
  econstructor; econstructor; split.
  eapply eval_Efield_struct; eauto. rewrite typeof_simpl_expr; eauto.
  econstructor; eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut.
(* field union *)
  rewrite <- comp_env_preserved in *.
  exploit eval_simpl_expr; eauto. intros [tv [A B]].
  inversion B. subst.
  econstructor; econstructor; split.
  eapply eval_Efield_union; eauto. rewrite typeof_simpl_expr; eauto. auto.
Qed.

Lemma eval_simpl_exprlist:
  forall al tyl vl,
  eval_exprlist ge e le m al tyl vl ->
  compat_cenv (addr_taken_exprlist al) cenv ->
  val_casted_list vl tyl /\
  exists tvl,
     eval_exprlist tge te tle tm (simpl_exprlist cenv al) tyl tvl
  /\ Val.inject_list f vl tvl.
Proof.
  induction 1; simpl; intros.
  split. constructor. econstructor; split. constructor. auto.
  exploit eval_simpl_expr; eauto with compat. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]].
  exploit IHeval_exprlist; eauto with compat. intros [E [tvl [F G]]].
  split. constructor; auto. eapply cast_val_is_casted; eauto.
  exists (tv2 :: tvl); split. econstructor; eauto.
  rewrite typeof_simpl_expr; auto.
  econstructor; eauto.
Qed.

End EVAL_EXPR.

(** Matching continuations *)

Inductive match_cont (f: meminj): compilenv -> cont -> cont -> mem -> sup -> sup -> Prop :=
  | match_Kstop: forall cenv m bound tbound hi,
      match_globalenvs f hi -> Mem.sup_include hi bound -> Mem.sup_include hi tbound ->
      match_cont f cenv Kstop Kstop m bound tbound
  | match_Kseq: forall cenv s k ts tk m bound tbound,
      simpl_stmt cenv s = OK ts ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (addr_taken_stmt s) cenv ->
      match_cont f cenv (Kseq s k) (Kseq ts tk) m bound tbound
  | match_Kloop1: forall cenv s1 s2 k ts1 ts2 tk m bound tbound,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk) m bound tbound
  | match_Kloop2: forall cenv s1 s2 k ts1 ts2 tk m bound tbound,
      simpl_stmt cenv s1 = OK ts1 ->
      simpl_stmt cenv s2 = OK ts2 ->
      match_cont f cenv k tk m bound tbound ->
      compat_cenv (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)) cenv ->
      match_cont f cenv (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk) m bound tbound
  | match_Kswitch: forall cenv k tk m bound tbound,
      match_cont f cenv k tk m bound tbound ->
      match_cont f cenv (Kswitch k) (Kswitch tk) m bound tbound
  | match_Kcall: forall cenv optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound x,
      transf_function fn = OK tfn ->
      match_envs f (cenv_for fn) e le m lo hi te tle tlo thi ->
      match_cont f (cenv_for fn) k tk m lo tlo ->
      check_opttemp (cenv_for fn) optid = OK x ->
      Mem.sup_include hi bound -> Mem.sup_include thi tbound ->
      match_cont f cenv (Kcall optid fn e le k)
                        (Kcall optid tfn te tle tk) m bound tbound.

(** Invariance property by change of memory and injection *)

Lemma match_cont_invariant:
  forall f' m' f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  (forall b chunk v,
    f b = None -> sup_In b bound -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  inject_incr f f' ->
  (forall b, sup_In b bound -> f' b = f b) ->
  (forall b b' delta, f' b = Some(b', delta) -> sup_In b' tbound -> f' b = f b) ->
  match_cont f' cenv k tk m' bound tbound.
Proof.
  induction 1; intros LOAD INCR INJ1 INJ2; econstructor; eauto.
(* globalenvs *)
  inv H. constructor; intros; eauto.
  assert (f b1 = Some (b2, delta)). rewrite <- H; symmetry; eapply INJ2; eauto.
  auto.
  eapply IMAGE; eauto.
(* call *)
  eapply match_envs_invariant; eauto.
  intros. apply LOAD; auto. destruct H6. auto.
  intros. apply INJ1; auto. destruct H5. auto.
  intros. eapply INJ2; eauto. destruct H6. auto.
  eapply IHmatch_cont; eauto.
  intros; apply LOAD; auto. inv H0. auto.
  intros; apply INJ1. inv H0. auto.
  intros; eapply INJ2; eauto. inv H0; auto.
Qed.

(** Invariance by assignment to location "above" *)

Lemma match_cont_assign_loc:
  forall f cenv k tk m bound tbound ty loc ofs v m',
  match_cont f cenv k tk m bound tbound ->
  assign_loc ge ty m loc ofs v m' ->
  ~ sup_In loc bound ->
  match_cont f cenv k tk m' bound tbound.
Proof.
  intros. eapply match_cont_invariant; eauto.
  intros. rewrite <- H4. inv H0.
  (* scalar *)
  simpl in H6. eapply Mem.load_store_other; eauto. left. congruence.
  (* block copy *)
  eapply Mem.load_storebytes_other; eauto. left. congruence.
Qed.

(** Invariance by external calls *)

Lemma match_cont_extcall:
  forall f cenv k tk m bound tbound tm f' m',
  match_cont f cenv k tk m bound tbound ->
  Mem.unchanged_on (loc_unmapped f) m m' ->
  inject_incr f f' ->
  inject_separated f f' m tm ->
  Mem.sup_include bound (Mem.support m) -> Mem.sup_include tbound (Mem.support tm) ->
  match_cont f' cenv k tk m' bound tbound.
Proof.
  intros. eapply match_cont_invariant; eauto.
  intros. eapply Mem.load_unchanged_on; eauto.
  red in H2. intros. destruct (f b) as [[b' delta] | ] eqn:?. auto.
  destruct (f' b) as [[b' delta] | ] eqn:?; auto.
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  apply H3 in H5. congruence.
  red in H2. intros. destruct (f b) as [[b'' delta''] | ] eqn:?. auto.
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  apply H4 in H6. congruence.
Qed.

(** Invariance by change of bounds *)

Lemma match_cont_incr_bounds:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  forall bound' tbound',
  Mem.sup_include bound bound' -> Mem.sup_include tbound tbound' ->
  match_cont f cenv k tk m bound' tbound'.
Proof.
  induction 1; intros; econstructor; eauto; auto.
  apply Mem.sup_include_trans with bound. auto. auto.
  apply Mem.sup_include_trans with tbound. auto. auto.
  apply Mem.sup_include_trans with bound. auto. auto.
  apply Mem.sup_include_trans with tbound. auto. auto.
Qed.

(** [match_cont] and call continuations. *)

Lemma match_cont_change_cenv:
  forall f cenv k tk m bound tbound cenv',
  match_cont f cenv k tk m bound tbound ->
  is_call_cont k ->
  match_cont f cenv' k tk m bound tbound.
Proof.
  intros. inv H; simpl in H0; try contradiction; econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  is_call_cont k ->
  is_call_cont tk.
Proof.
  intros. inv H; auto.
Qed.

Lemma match_cont_call_cont:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  forall cenv',
  match_cont f cenv' (call_cont k) (call_cont tk) m bound tbound.
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

(** [match_cont] and freeing of environment blocks *)

Remark free_list_support:
  forall l m m',
  Mem.free_list m l = Some m' -> Mem.support m' = Mem.support m.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.support m1). eauto. eapply Mem.support_free; eauto.
Qed.

Remark free_list_load:
  forall chunk b' l m m',
  Mem.free_list m l = Some m' ->
  (forall b lo hi, In (b, lo, hi) l ->  b'<> b) ->
  Mem.valid_block m b' ->
  Mem.load chunk m' b' 0 = Mem.load chunk m b' 0.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.load chunk m1 b' 0).
  apply IHl. auto. eauto. auto. eapply Mem.valid_block_free_1. eauto. auto.
  eapply Mem.load_free. eauto. left. eauto.
Qed.

Lemma match_cont_free_env:
  forall f cenv e le m lo hi te tle tm tlo thi k tk m' tm',
  match_envs f cenv e le m lo hi te tle tlo thi ->
  match_cont f cenv k tk m lo tlo ->
  Mem.sup_include hi (Mem.support m) ->
  Mem.sup_include thi (Mem.support tm) ->
  Mem.free_list m (blocks_of_env ge e) = Some m' ->
  Mem.free_list tm (blocks_of_env tge te) = Some tm' ->
  match_cont f cenv k tk m' (Mem.support m') (Mem.support tm').
Proof.
  intros. apply match_cont_incr_bounds with lo tlo.
  eapply match_cont_invariant; eauto.
  intros. rewrite <- H7. eapply free_list_load; eauto.
  unfold blocks_of_env; intros. exploit list_in_map_inv; eauto.
  intros [[id [b1 ty]] [P Q]]. simpl in P. inv P.
  exploit me_range; eauto. eapply PTree.elements_complete; eauto.
  intros [A B]. congruence. eapply Mem.valid_access_valid_block.
  apply Mem.load_valid_access in H7. eapply Mem.valid_access_implies in H7.
  eauto. constructor.
  rewrite (free_list_support _ _ _ H3). inv H; auto.
  apply Mem.sup_include_trans with hi. auto. auto.
  rewrite (free_list_support _ _ _ H4). inv H; auto.
  apply Mem.sup_include_trans with thi. auto. auto.
Qed.

(** Matching of global environments *)

Lemma match_cont_globalenv:
  forall f cenv k tk m bound tbound,
  match_cont f cenv k tk m bound tbound ->
  exists bound, match_globalenvs f bound.
Proof.
  induction 1; auto. exists hi; auto.
Qed.

Hint Resolve match_cont_globalenv: compat.

Lemma match_cont_find_funct:
  forall f cenv k tk m bound tbound vf fd tvf,
  match_cont f cenv k tk m bound tbound ->
  Genv.find_funct ge vf = Some fd ->
  Val.inject f vf tvf ->
  exists tfd, Genv.find_funct tge tvf = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  intros. exploit match_cont_globalenv; eauto. intros [bound1 MG]. destruct MG.
  inv H1; simpl in H0; try discriminate. destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero); try discriminate.
  subst ofs1.
  assert (f b1 = Some(b1, 0)).
    apply DOMAIN. eapply FUNCTIONS; eauto.
  rewrite H1 in H2; inv H2.
  rewrite Ptrofs.add_zero. simpl. rewrite dec_eq_true. apply function_ptr_translated; auto.
Qed.

(** Relating execution states *)

Inductive match_states: state -> state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk te tle tm j lo hi tlo thi
        (TRF: transf_function f = OK tf)
        (TRS: simpl_stmt (cenv_for f) s = OK ts)
        (MENV: match_envs j (cenv_for f) e le m lo hi te tle tlo thi)
        (MCONT: match_cont j (cenv_for f) k tk m lo tlo)
        (MINJ: Mem.inject j m tm)
        (VINJ: j = struct_meminj (Mem.support m))
        (MSTK: Mem.stackseq m tm)
        (COMPAT: compat_cenv (addr_taken_stmt s) (cenv_for f))
        (BOUND: Mem.sup_include hi (Mem.support m))
        (TBOUND: Mem.sup_include thi (Mem.support tm)),
      match_states (State f s k e le m)
                   (State tf ts tk te tle tm)
  | match_call_state:
      forall fd vargs k m tfd tvargs tk tm j targs tres cconv id
        (TRFD: transf_fundef fd = OK tfd)
        (MCONT: forall cenv, match_cont j cenv k tk m (Mem.support m) (Mem.support tm))
        (FIND: Genv.find_funct_ptr ge (Global id) = Some fd)
        (MINJ: Mem.inject j m tm)
        (VINJ: j = struct_meminj (Mem.support m))
        (MSTK: Mem.stackseq m tm)
        (AINJ: Val.inject_list j vargs tvargs)
        (FUNTY: type_of_fundef fd = Tfunction targs tres cconv)
        (ANORM: val_casted_list vargs targs),
      match_states (Callstate fd vargs k m id)
                   (Callstate tfd tvargs tk tm id)
  | match_return_state:
      forall v k m tv tk tm j
        (MCONT: forall cenv, match_cont j cenv k tk m (Mem.support m) (Mem.support tm))
        (MINJ: Mem.inject j m tm)
        (VINJ: j = struct_meminj (Mem.support m))
        (MSTK: Mem.stackseq m tm)
        (RINJ: Val.inject j v tv),
      match_states (Returnstate v k m)
                   (Returnstate tv tk tm).

(** The simulation diagrams *)

Remark is_liftable_var_charact:
  forall cenv a,
  match is_liftable_var cenv a with
  | Some id => exists ty, a = Evar id ty /\ VSet.mem id cenv = true
  | None => match a with Evar id ty => VSet.mem id cenv = false | _ => True end
  end.
Proof.
  intros. destruct a; simpl; auto.
  destruct (VSet.mem i cenv) eqn:?.
  exists t; auto.
  auto.
Qed.

Remark simpl_select_switch:
  forall cenv n ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_lblstmt cenv (select_switch n ls) = OK (select_switch n tls).
Proof.
  intros cenv n.
  assert (DFL:
    forall ls tls,
    simpl_lblstmt cenv ls = OK tls ->
    simpl_lblstmt cenv (select_switch_default ls) = OK (select_switch_default tls)).
  {
    induction ls; simpl; intros; monadInv H.
    auto.
    simpl. destruct o. eauto. simpl; rewrite EQ, EQ1. auto.
  }
  assert (CASE:
    forall ls tls,
    simpl_lblstmt cenv ls = OK tls ->
    match select_switch_case n ls with
    | None => select_switch_case n tls = None
    | Some ls' =>
        exists tls', select_switch_case n tls = Some tls' /\ simpl_lblstmt cenv ls' = OK tls'
    end).
  {
    induction ls; simpl; intros; monadInv H; simpl.
    auto.
    destruct o.
    destruct (zeq z n).
    econstructor; split; eauto. simpl; rewrite EQ, EQ1; auto.
    apply IHls. auto.
    apply IHls. auto.
  }
  intros; unfold select_switch.
  specialize (CASE _ _ H). destruct (select_switch_case n ls) as [ls'|].
  destruct CASE as [tls' [P Q]]. rewrite P, Q. auto.
  rewrite CASE. apply DFL; auto.
Qed.

Remark simpl_seq_of_labeled_statement:
  forall cenv ls tls,
  simpl_lblstmt cenv ls = OK tls ->
  simpl_stmt cenv (seq_of_labeled_statement ls) = OK (seq_of_labeled_statement tls).
Proof.
  induction ls; simpl; intros; monadInv H; simpl.
  auto.
  rewrite EQ; simpl. erewrite IHls; eauto. simpl. auto.
Qed.

Remark compat_cenv_select_switch:
  forall cenv n ls,
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  compat_cenv (addr_taken_lblstmt (select_switch n ls)) cenv.
Proof.
  intros cenv n.
  assert (DFL: forall ls,
    compat_cenv (addr_taken_lblstmt ls) cenv ->
    compat_cenv (addr_taken_lblstmt (select_switch_default ls)) cenv).
  {
    induction ls; simpl; intros.
    eauto with compat.
    destruct o; simpl; eauto with compat.
  }
  assert (CASE: forall ls ls',
    compat_cenv (addr_taken_lblstmt ls) cenv ->
    select_switch_case n ls = Some ls' ->
    compat_cenv (addr_taken_lblstmt ls') cenv).
  {
    induction ls; simpl; intros.
    discriminate.
    destruct o. destruct (zeq z n). inv H0. auto. eauto with compat.
    eauto with compat.
  }
  intros. specialize (CASE ls). unfold select_switch.
  destruct (select_switch_case n ls) as [ls'|]; eauto.
Qed.

Remark addr_taken_seq_of_labeled_statement:
  forall ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls.
Proof.
  induction ls; simpl; congruence.
Qed.

Section FIND_LABEL.

Variable f: meminj.
Variable cenv: compilenv.
Variable m: mem.
Variables bound tbound: sup.
Variable lbl: ident.

Lemma simpl_find_label:
  forall s k ts tk,
  simpl_stmt cenv s = OK ts ->
  match_cont f cenv k tk m bound tbound ->
  compat_cenv (addr_taken_stmt s) cenv ->
  match find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk',
         find_label lbl ts tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m bound tbound
  end

with simpl_find_label_ls:
  forall ls k tls tk,
  simpl_lblstmt cenv ls = OK tls ->
  match_cont f cenv k tk m bound tbound ->
  compat_cenv (addr_taken_lblstmt ls) cenv ->
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl tls tk = None
  | Some(s', k') =>
      exists ts', exists tk',
         find_label_ls lbl tls tk = Some(ts', tk')
      /\ compat_cenv (addr_taken_stmt s') cenv
      /\ simpl_stmt cenv s' = OK ts'
      /\ match_cont f cenv k' tk' m bound tbound
  end.

Proof.
  induction s; simpl; intros until tk; intros TS MC COMPAT; auto.
  (* skip *)
  monadInv TS; auto.
  (* var *)
  destruct (is_liftable_var cenv e); monadInv TS; auto.
  unfold Sset_debug. destruct (Compopts.debug tt); auto.
  (* set *)
  monadInv TS; auto.
  (* call *)
  monadInv TS; auto.
  (* builtin *)
  monadInv TS; auto.
  (* seq *)
  monadInv TS.
  exploit (IHs1 (Kseq s2 k) x (Kseq x0 tk)); eauto with compat.
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kseq s2 k)) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto.
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* ifthenelse *)
  monadInv TS.
  exploit (IHs1 k x tk); eauto with compat.
  destruct (find_label lbl s1 k) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl. rewrite P. auto.
  intros E. simpl. rewrite E. eapply IHs2; eauto with compat.
  (* loop *)
  monadInv TS.
  exploit (IHs1 (Kloop1 s1 s2 k) x (Kloop1 x x0 tk)); eauto with compat.
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kloop1 s1 s2 k)) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'. simpl; rewrite P. auto.
  intros E. simpl; rewrite E. eapply IHs2; eauto with compat. econstructor; eauto with compat.
  (* break *)
  monadInv TS; auto.
  (* continue *)
  monadInv TS; auto.
  (* return *)
  monadInv TS; auto.
  (* switch *)
  monadInv TS. simpl.
  eapply simpl_find_label_ls; eauto with compat. constructor; auto.
  (* label *)
  monadInv TS. simpl.
  destruct (ident_eq lbl l).
  exists x; exists tk; auto.
  eapply IHs; eauto.
  (* goto *)
  monadInv TS; auto.

  induction ls; simpl; intros.
  (* nil *)
  monadInv H. auto.
  (* cons *)
  monadInv H.
  exploit (simpl_find_label s (Kseq (seq_of_labeled_statement ls) k)).
    eauto. constructor. eapply simpl_seq_of_labeled_statement; eauto. eauto.
    rewrite addr_taken_seq_of_labeled_statement. eauto with compat.
    eauto with compat.
  destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[s' k']|].
  intros [ts' [tk' [P [Q [R S]]]]]. exists ts'; exists tk'; split. simpl; rewrite P. auto. auto.
  intros E. simpl; rewrite E. eapply IHls; eauto with compat.
Qed.

Lemma find_label_store_params:
  forall s k params, find_label lbl (store_params cenv params s) k = find_label lbl s k.
Proof.
  induction params; simpl. auto.
  destruct a as [id ty]. destruct (VSet.mem id cenv); auto.
Qed.

Lemma find_label_add_debug_vars:
  forall s k vars, find_label lbl (add_debug_vars vars s) k = find_label lbl s k.
Proof.
  unfold add_debug_vars. destruct (Compopts.debug tt); auto.
  induction vars; simpl; auto. destruct a as [id ty]; simpl. auto.
Qed.

Lemma find_label_add_debug_params:
  forall s k vars, find_label lbl (add_debug_params vars s) k = find_label lbl s k.
Proof.
  unfold add_debug_params. destruct (Compopts.debug tt); auto.
  induction vars; simpl; auto. destruct a as [id ty]; simpl. auto.
Qed.

End FIND_LABEL.

(*
Lemma sinj_external_call :
  forall m m' tm tm' f f' vargs tvargs vres tvres ef ge t,
    Mem.inject f m tm ->
    Mem.stackseq m tm ->
    external_call ef ge vargs m t vres m' ->
    external_call ef ge tvargs tm t tvres tm' ->
    Val.inject_list f vargs tvargs ->
    Mem.inject f' m' tm' ->
    f = struct_meminj (Mem.support m) ->
    Mem.stackseq m' tm' /\
    f' = struct_meminj (Mem.support m').
Proof.
*)

Lemma step_simulation:
  forall S1 t S2, step1 ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step2 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; simpl; intros; inv MS; simpl in *; try (monadInv TRS).

(* assign *)
  generalize (is_liftable_var_charact (cenv_for f) a1); destruct (is_liftable_var (cenv_for f) a1) as [id|]; monadInv TRS.
  (* liftable *)
  intros [ty [P Q]]; subst a1; simpl in *.
  exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
  exploit sem_cast_inject; eauto. intros [tv [C D]].
  exploit me_vars; eauto. instantiate (1 := id). intros MV.
  inv H.
  (* local variable *)
  econstructor; split.
  eapply step_Sset_debug. eauto. rewrite typeof_simpl_expr. eauto.
  econstructor; eauto with compat.
  erewrite assign_loc_support; eauto.
  eapply match_envs_assign_lifted; eauto.
  eapply cast_val_is_casted; eauto.
  erewrite assign_loc_support; eauto.
  eapply match_cont_assign_loc; eauto. exploit me_range; eauto. intros [E F]. auto.
  erewrite assign_loc_support; eauto.
  inv MV; try congruence. inv H2; try congruence. unfold Mem.storev in H3.
  eapply Mem.store_unmapped_inject; eauto. congruence.
  unfold Mem.stackseq in *. erewrite assign_loc_support; eauto.
  erewrite assign_loc_support; eauto.
  (* global variable *)
  inv MV; congruence.
  (* not liftable *)
  intros P.
  exploit eval_simpl_lvalue; eauto with compat. intros [tb [tofs [E F]]].
  exploit eval_simpl_expr; eauto with compat. intros [tv2 [A B]].
   exploit sem_cast_inject; eauto. intros [tv [C D]].
  exploit assign_loc_inject; eauto. intros [tm' [X [Y Z]]].
  econstructor; split.
  apply plus_one. econstructor. eexact E. eexact A. repeat rewrite typeof_simpl_expr. eexact C.
  rewrite typeof_simpl_expr; auto. eexact X.
  econstructor; eauto with compat.
  eapply match_envs_invariant; eauto.
  eapply match_cont_invariant; eauto.
  erewrite <- assign_loc_support; eauto.
  unfold Mem.stackseq in *.
  rewrite (assign_loc_support _ _ _ _ _ _ _ X); eauto.
  erewrite assign_loc_support; eauto.
  erewrite assign_loc_support; eauto.
  erewrite assign_loc_support; eauto.

(* set temporary *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  econstructor; split.
  apply plus_one. econstructor. eauto.
  econstructor; eauto with compat.
  eapply match_envs_set_temp; eauto.

(* call *)
  exploit eval_simpl_expr; eauto with compat. intros [tvf [A B]].
  exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
  exploit match_cont_find_funct; eauto.
  simpl. destr. eauto.
  intros [tfd [P Q]].
  econstructor; split.
  apply plus_one. eapply step_call with (fd := tfd).
  rewrite typeof_simpl_expr. eauto.
  instantiate (1:=id).
  instantiate (1:=tvf).
  inv B. unfold struct_meminj in H6. destr_in H6. simpl in H6. inv H6.
  auto. eauto. eauto. eauto.
  erewrite type_of_fundef_preserved; eauto.
  econstructor; eauto.
  intros. econstructor; eauto.

(* builtin *)
  exploit eval_simpl_exprlist; eauto with compat. intros [CASTED [tvargs [C D]]].
  exploit external_call_mem_inject'; eauto. apply match_globalenvs_preserves_globals; eauto with compat.
  intros [j' [tvres [tm' [P [Q [R [S [T [U [V [W X]]]]]]]]]]].
  (* exploit sinj_external_call. apply MINJ. all: eauto. intros [Y Z]. *)
  econstructor; split.
  apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto with compat.
  eapply match_envs_set_opttemp; eauto.
  eapply match_envs_extcall; eauto.
  eapply match_cont_extcall; eauto.
  inv MENV. eapply Mem.sup_include_trans. eauto. eauto.
  inv MENV; eapply Mem.sup_include_trans. eauto. eauto.
  {
    apply Axioms.extensionality. intro b.
    destruct ((struct_meminj (Mem.support m)) b) eqn:Z. destruct p.
    - apply U in Z as Z'. rewrite Z'. rewrite <- Z.
      unfold struct_meminj. destr. exploit external_call_valid_block.
      apply H0. eauto. intro. destr. apply n in H1. inv H1.
      inv MINJ. exploit mi_freeblocks; eauto. intro. congruence.
    - destruct (j' b) eqn:Z1.
      + destruct p. exploit W; eauto.
      intros [A1 B1]. inv R. unfold struct_meminj. destr.
      exploit X; eauto. intros [C1 D1]. rewrite Z1 in D1. inv D1.
      destruct b. destruct f0; simpl in C1. inv C1. simpl. auto. inv C1.
      apply mi_freeblocks in n. congruence.
      + unfold struct_meminj. destr. unfold struct_meminj in Z. destr_in Z.
      exploit X; eauto. intros [C1 D1]. congruence.
  }
  eapply external_call_mem_inject_stackseq; eauto. eapply match_globalenvs_preserves_globals. eauto with compat.
  eapply Mem.sup_include_trans; eauto. eapply external_call_support; eauto.
  eapply Mem.sup_include_trans; eauto. eapply external_call_support; eauto.

(* sequence *)
  econstructor; split. apply plus_one. econstructor.
  econstructor; eauto with compat. econstructor; eauto with compat.

(* skip sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* continue sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* break sequence *)
  inv MCONT. econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* ifthenelse *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v1 := tv) (b := b). auto.
  rewrite typeof_simpl_expr. eapply bool_val_inject; eauto.
  destruct b; econstructor; eauto with compat.

(* loop *)
  econstructor; split. apply plus_one. econstructor. econstructor; eauto with compat. econstructor; eauto with compat.

(* skip-or-continue loop *)
  inv MCONT. econstructor; split.
  apply plus_one. econstructor. destruct H; subst x; simpl in *; intuition congruence.
  econstructor; eauto with compat. econstructor; eauto with compat.

(* break loop1 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop1.
  econstructor; eauto.

(* skip loop2 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_skip_loop2.
  econstructor; eauto with compat. simpl; rewrite H2; rewrite H4; auto.

(* break loop2 *)
  inv MCONT. econstructor; split. apply plus_one. eapply step_break_loop2.
  econstructor; eauto.

(* return none *)
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  assert (Mem.stackseq m' tm'). unfold Mem.stackseq in *.
  rewrite (free_list_support _ _ _ H).
  rewrite (free_list_support _ _ _ P). auto.
  exploit Mem.return_frame_parallel_stackseq; eauto.  intros [tm'' [P' Q']].
  exploit Mem.return_frame_inject; eauto. intro.
  econstructor; split. apply plus_one. econstructor; eauto.
  econstructor; eauto.
  intros. eapply match_cont_call_cont.
  eapply match_cont_invariant.
  eapply match_cont_incr_bounds.
  eapply match_cont_free_env; eauto.
  intro. eapply Mem.support_return_frame_1 in H0. apply H0.
  intro. eapply Mem.support_return_frame_1 in P'. apply P'.
  intros. erewrite Mem.load_return_frame; eauto.
  eauto. eauto. eauto.
  eapply sinj_refl. erewrite <- free_list_support; eauto.
  intro. eapply Mem.support_return_frame_1 in H0. apply H0.

(* return some *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  exploit sem_cast_inject; eauto. intros [tv' [C D]].
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  assert (Mem.stackseq m' tm'). unfold Mem.stackseq in *.
  rewrite (free_list_support _ _ _ H1).
  rewrite (free_list_support _ _ _ P). auto.
  exploit Mem.return_frame_parallel_stackseq; eauto.  intros [tm'' [P' Q']].
  exploit Mem.return_frame_inject; eauto. intro.
  econstructor; split. apply plus_one. econstructor; eauto.
  rewrite typeof_simpl_expr. monadInv TRF; simpl. eauto.
  econstructor; eauto.
  intros. eapply match_cont_call_cont.
  eapply match_cont_invariant.
  eapply match_cont_incr_bounds.
  eapply match_cont_free_env; eauto.
  intro. eapply Mem.support_return_frame_1 in H2. apply H2.
  intro. eapply Mem.support_return_frame_1 in P'. apply P'.
  intros. erewrite Mem.load_return_frame; eauto.
  eauto. eauto. eauto.
  eapply sinj_refl. erewrite <- free_list_support; eauto.
  intro. eapply Mem.support_return_frame_1 in H2. apply H2.

(* skip call *)
  exploit match_envs_free_blocks; eauto. intros [tm'1 [P Q]].
  assert (Mem.stackseq m' tm'1). unfold Mem.stackseq in *.
  rewrite (free_list_support _ _ _ H0).
  rewrite (free_list_support _ _ _ P). auto.
  exploit Mem.return_frame_parallel_stackseq; eauto.  intros [tm'' [P' Q']].
  exploit Mem.return_frame_inject; eauto. intro.
  econstructor; split. apply plus_one. econstructor; eauto.
  eapply match_cont_is_call_cont; eauto.
  monadInv TRF; auto.
  econstructor; eauto.
  intros. apply match_cont_change_cenv with (cenv_for f); auto.
  eapply match_cont_invariant.
  eapply match_cont_incr_bounds.
  eapply match_cont_free_env; eauto.
  intro. eapply Mem.support_return_frame_1 in H1. apply H1.
  intro. eapply Mem.support_return_frame_1 in P'. apply P'.
  intros. erewrite Mem.load_return_frame; eauto.
  eauto. eauto. eauto.
  eapply sinj_refl. erewrite <- free_list_support; eauto.
  intro. eapply Mem.support_return_frame_1 in H1. apply H1.

(* switch *)
  exploit eval_simpl_expr; eauto with compat. intros [tv [A B]].
  econstructor; split. apply plus_one. econstructor; eauto.
  rewrite typeof_simpl_expr. instantiate (1 := n).
  unfold sem_switch_arg in *;
  destruct (classify_switch (typeof a)); try discriminate;
  inv B; inv H0; auto.
  econstructor; eauto.
  erewrite simpl_seq_of_labeled_statement. reflexivity.
  eapply simpl_select_switch; eauto.
  econstructor; eauto. rewrite addr_taken_seq_of_labeled_statement.
  apply compat_cenv_select_switch. eauto with compat.

(* skip-break switch *)
  inv MCONT. econstructor; split.
  apply plus_one. eapply step_skip_break_switch. destruct H; subst x; simpl in *; intuition congruence.
  econstructor; eauto with compat.

(* continue switch *)
  inv MCONT. econstructor; split.
  apply plus_one. eapply step_continue_switch.
  econstructor; eauto with compat.

(* label *)
  econstructor; split. apply plus_one. econstructor. econstructor; eauto.

(* goto *)
  generalize TRF; intros TRF'. monadInv TRF'.
  exploit (simpl_find_label (struct_meminj (Mem.support m)) (cenv_for f) m lo tlo lbl (fn_body f) (call_cont k) x (call_cont tk)).
    eauto. eapply match_cont_call_cont. eauto.
    apply compat_cenv_for.
  rewrite H. intros [ts' [tk' [A [B [C D]]]]].
  econstructor; split.
  apply plus_one. econstructor; eauto. simpl.
  rewrite find_label_add_debug_params. rewrite find_label_store_params. rewrite find_label_add_debug_vars. eexact A.
  econstructor; eauto.

(* internal function *)
  monadInv TRFD. inv H.
  generalize EQ; intro EQ'; monadInv EQ'.
  assert (list_norepet (var_names (fn_params f ++ fn_vars f))).
    unfold var_names. rewrite map_app. auto.
  exploit Mem.alloc_frame_parallel_inject; eauto.
  intros (tm' & p' & ALL & INJ).
  exploit alloc_var_var'; eauto. intros (blocks & VARS' & H4).
  exploit nextblock_pos_1. apply H1. intro.
  exploit nextblock_pos_1; eauto. intro.
  exploit Mem.alloc_frame_parallel_stackseq; eauto. intro. inv H7.
  exploit match_envs_alloc_variables; eauto.
    instantiate (1 := cenv_for_gen (addr_taken_stmt f.(fn_body)) (fn_params f ++ fn_vars f)).
    intros. eapply cenv_for_gen_by_value; eauto. rewrite VSF.mem_iff. eexact H8.
    intros. eapply cenv_for_gen_domain. rewrite VSF.mem_iff. eexact H7.
  intros [j' [te [tm'' [A [B [C [D [E [F [G I]]]]]]]]]].
  assert (K: list_forall2 val_casted vargs (map snd (fn_params f))).
  { apply val_casted_list_params. unfold type_of_function in FUNTY. congruence. }
  exploit store_params_correct.
    eauto.
    eapply list_norepet_append_left; eauto.
    eexact K.
    apply val_inject_list_incr with j'; eauto.
    eexact B. eexact C.
    intros. apply (create_undef_temps_lifted id0 f). auto.
    intros. destruct (create_undef_temps (fn_temps f))!id0 as [v|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [P Q]. elim (l id0 id0); auto.
  intros [tel [tm1 [P [Q [R [S T]]]]]].
  change (cenv_for_gen (addr_taken_stmt (fn_body f)) (fn_params f ++ fn_vars f))
    with (cenv_for f) in *.
  generalize (vars_and_temps_properties (cenv_for f) (fn_params f) (fn_vars f) (fn_temps f)).
  intros [X [Y Z]]. auto. auto.
  econstructor; split.
  eapply plus_left. econstructor.
  econstructor. exact Y. exact X. exact Z. eauto. simpl. eexact A. simpl. eexact Q.
  simpl. eapply star_trans. eapply step_add_debug_params. auto. eapply forall2_val_casted_inject; eauto. eexact Q.
  eapply star_trans. eexact P. eapply step_add_debug_vars.
  unfold remove_lifted; intros. rewrite List.filter_In in H7. destruct H7.
  apply negb_true_iff in H8. eauto.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto.
  eapply match_cont_invariant with (m:= m); eauto.
  eapply match_cont_incr_bounds; eauto.
  intro. eapply Mem.support_alloc_frame_1 in H1. apply H1.
  intro. eapply Mem.support_alloc_frame_1 in ALL. apply ALL.
  intros. transitivity (Mem.load chunk m2 b 0).
  eapply bind_parameters_load; eauto. intros.
  exploit alloc_variables_range. eexact H2. eauto.
  unfold empty_env. rewrite PTree.gempty. intros [?|?]. congruence.
  red; intros; subst b'. destruct H12. congruence.
  eapply alloc_variables_load; eauto.
  erewrite Mem.load_alloc_frame; eauto.
{
  apply Axioms.extensionality. intro b0.
  destruct (Mem.sup_dec b0 (Mem.support m0)).
  - rewrite E. unfold struct_meminj.
    eapply Mem.support_alloc_frame_1 in H1 as SUP1.
    apply SUP1 in s as s1.
    eapply alloc_variables_support in s as s2; eauto.
    erewrite <- bind_parameters_support in s2; eauto.
    destr; destr; try congruence. auto.
  - destruct (Mem.sup_dec b0 (Mem.support m1)).
    + unfold struct_meminj. destr.
      erewrite bind_parameters_support in s; eauto.
      unfold unchecked_meminj.
      exploit alloc_vars_inv'. apply VARS'. intro. apply H7 in s.
      destruct s; try congruence.
      assert (Mem.nextblock m0 = Stack (Some id) p' 1%positive).
      eapply Mem.alloc_frame_nextblock; eauto.
      exploit nextblock_alloc_vars; eauto.
      intros (p'0 & X' & Y').
      destruct H10. subst. unfold find_func_pos.
      rewrite FIND.
      exploit I. eauto. intro.
      destruct H10 as (id0 & path0 & pos & X1 & Y1).
      rewrite Y1. inv X1. auto.
    + inv C. rewrite mi_freeblocks; eauto. unfold struct_meminj.
      destr; try congruence.
      erewrite bind_parameters_support in n0; eauto.
}
  unfold Mem.stackseq in *. rewrite T.
  erewrite bind_parameters_support; eauto.
  eapply alloc_variables_parallel_stackseq; eauto.
  apply compat_cenv_for.
  rewrite (bind_parameters_support _ _ _ _ _ _ H3). apply Mem.sup_include_refl.
  rewrite T; auto. apply Mem.sup_include_refl.

(* external function *)
  monadInv TRFD. inv FUNTY.
  exploit external_call_mem_inject'; eauto. apply match_globalenvs_preserves_globals.
  eapply match_cont_globalenv. eexact (MCONT VSet.empty).
  intros [j' [tvres [tm' [P [Q [R [S [T [U [V [W X]]]]]]]]]]].
(*  exploit sinj_external_call. apply MINJ. all: eauto. intros [X Y]. *)
  econstructor; split.
  apply plus_one. econstructor; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  intros. apply match_cont_incr_bounds with (Mem.support m) (Mem.support tm).
  eapply match_cont_extcall; eauto.
  apply Mem.sup_include_refl. apply Mem.sup_include_refl.
  eapply external_call_support; eauto.
  eapply external_call_support; eauto.
  {
    apply Axioms.extensionality. intro b.
    destruct ((struct_meminj (Mem.support m)) b) eqn:Z. destruct p.
    - apply U in Z as Z'. rewrite Z'. rewrite <- Z.
      unfold struct_meminj. destr. exploit external_call_valid_block.
      apply H. eauto. intro. destr. apply n in H0. inv H0.
      inv MINJ. exploit mi_freeblocks; eauto. intro. congruence.
    - destruct (j' b) eqn:Z1.
      + destruct p. exploit W; eauto.
      intros [A1 B1]. inv R. unfold struct_meminj. destr.
      exploit X; eauto. intros [C1 D1]. rewrite Z1 in D1. inv D1.
      destruct b. destruct f; simpl in C1. inv C1. simpl. auto. inv C1.
      apply mi_freeblocks in n. congruence.
      + unfold struct_meminj. destr. unfold struct_meminj in Z. destr_in Z.
      exploit X; eauto. intros [C1 D1]. congruence.
  }
  eapply external_call_mem_inject_stackseq; eauto. eapply match_globalenvs_preserves_globals.   eapply match_cont_globalenv. eexact (MCONT VSet.empty).
(* return *)
  specialize (MCONT (cenv_for f)). inv MCONT.
  econstructor; split.
  apply plus_one. econstructor.
  econstructor; eauto with compat.
  eapply match_envs_set_opttemp; eauto.
Qed.

Lemma initial_states_simulation:
  forall S, initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  assert (struct_meminj (Mem.support m0) = Mem.flat_inj (Mem.support m0)).
  apply Axioms.extensionality. intro x.
  unfold struct_meminj. unfold Mem.flat_inj.
  destruct (Mem.sup_dec x (Mem.support m0)); auto.
  unfold unchecked_meminj. destruct x. simpl in s.
  erewrite Genv.init_mem_stack in s; eauto.
  destruct p. inv s. inv H4. simpl in s. destruct n; simpl in s; inv s.
  auto.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial (proj1 TRANSF)). eauto.
  replace (prog_main tprog) with (prog_main prog).
  instantiate (1 := b). rewrite <- H1. apply symbols_preserved.
  generalize (match_program_main (proj1 TRANSF)). simpl; auto.
  eauto.
  rewrite <- H3; apply type_of_fundef_preserved; auto.
  replace (prog_main tprog) with (prog_main prog).
  econstructor; eauto.
  intros.
  rewrite H.
  econstructor. instantiate (1 := Mem.support m0).
  constructor; intros.
  unfold Mem.flat_inj. apply pred_dec_true; auto.
  unfold Mem.flat_inj in H4. destruct (Mem.sup_dec b1 (Mem.support m0)); inv H4.
  auto.
  eapply Genv.find_symbol_not_fresh; eauto.
  eapply Genv.find_funct_ptr_not_fresh; eauto.
  eapply Genv.find_var_info_not_fresh; eauto.
  apply Mem.sup_include_refl. apply Mem.sup_include_refl.
  apply Genv.genv_vars_eq in H1. subst. auto.
  rewrite H.
  eapply Genv.initmem_inject; eauto.
  apply struct_eq_refl.
  constructor.
  generalize (match_program_main (proj1 TRANSF)). simpl; auto.
Qed.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H.
  specialize (MCONT VSet.empty). inv MCONT.
  inv RINJ. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics1 prog) (semantics2 tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Qed.

End PRESERVATION.

(** ** Commutation with linking *)

Instance TransfSimplLocalsLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program; eauto.
- intros.
Local Transparent Linker_fundef.
  simpl in *; unfold link_fundef in *.
  destruct f1; monadInv H3; destruct f2; monadInv H4; try discriminate.
  destruct e; inv H2. exists (Internal x); split; auto. simpl; rewrite EQ; auto.
  destruct e; inv H2. exists (Internal x); split; auto. simpl; rewrite EQ; auto.
  destruct (external_function_eq e e0 && typelist_eq t t1 &&
            type_eq t0 t2 && calling_convention_eq c c0); inv H2.
  econstructor; split; eauto.
Qed.
