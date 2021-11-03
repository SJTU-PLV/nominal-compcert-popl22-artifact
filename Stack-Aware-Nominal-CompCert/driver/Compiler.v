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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require RTLmach.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.

(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require RTLmachproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
   @@ time "RTLmach" RTLmachproof.transf_program
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(* Definition transf_c_program_real p: res Asm.program :=
  transf_c_program p
  @@ time "SSAsm" SSAsmproof.transf_program.
  @@@ time "Translation from SSAsm to RealAsm" RealAsmgen.transf_program.
*)
(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass RTLmachproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(* Definition real_asm_passes :=
      mkpass SSAsmproof.match_prog
  ::: mkpass RealAsmproof.match_prog
  ::: pass_nil _. *)
(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Csyntax.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

Fixpoint passes_app {A B C} (l1: Passes A B) (l2: Passes B C) : Passes A C :=
  match l1 in (Passes AA BB) return (Passes BB C -> Passes AA C) with
  | pass_nil _ => fun l3 => l3
  | pass_cons _ _ _ P1 l1 => fun l2 => P1 ::: passes_app l1 l2
  end l2.

(* Definition match_prog_real :=
  pass_match (compose_passes (passes_app CompCert's_passes real_asm_passes)). *)

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p8' := RTLmachproof.transf_program p8) in *.
  set (p9 := Renumber.transf_program p8') in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  destruct (Asmgen.transf_program p20) as [p21|e] eqn:P21; simpl in T; try discriminate. inv T.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p8'; split. apply RTLmachproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
(*  exists p21; split. eapply SSAsmproof.transf_program_match; auto. *)
  reflexivity.
Qed.

Lemma compose_passes_app:
  forall {l1 l2} (A: Passes l1 l2) {l3} (B: Passes l2 l3) p tp,
    compose_passes (passes_app A B) p tp <->
    exists pi, compose_passes A p pi /\ compose_passes B pi tp.
Proof.
  induction A; simpl; intros. split. eexists; split; eauto.
  intros (pi & EQ & CP); inv EQ; auto.
  setoid_rewrite IHA. split; intro H; decompose [ex and] H; eauto.
Qed.
(*
Theorem transf_c_program_real_match:
  forall p tp,
    transf_c_program_real p = OK tp ->
    match_prog_real p tp.
Proof.
  intros p tp T. unfold transf_c_program_real in T.
  destruct (transf_c_program p) as [p1|e] eqn:TP; simpl in T; try discriminate. unfold time in T.
  destruct (RealAsmgen.transf_program p1) eqn:RTP; simpl in T; try discriminate. inv T.
(*  destruct (PseudoInstructions.check_program p0) eqn:CHK; simpl in T; try discriminate. inv T. *)
  unfold match_prog_real.
  rewrite compose_passes_app.
  fold match_prog. exists p1; split.
  eapply transf_c_program_match; eauto.
  simpl. eexists; split; eauto.
  eapply RealAsmproof.transf_program_match; eauto.
Qed.
*)

(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

Remark forward_simulation_identity:
  forall sem, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Lemma match_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

Definition fn_stack_requirements (tp: Asm.program) (id: ident) : Z :=
    match Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) (Values.Global id) with
    | Some (Internal f) => Asm.fn_stacksize f
    | _ => 0
    end.

Lemma match_program_no_more_functions:
  forall {F1 V1 F2 V2}
         `{Linker F1} `{Linker V1}
         Mf Mv
         (p1: program F1 V1) (p2: program F2 V2),
    match_program Mf Mv p1 p2 ->
    forall b,
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p1) b = None ->
    Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p2) b = None.
Proof.
  intros.
  generalize (Globalenvs.Genv.find_def_match_2 H1 b).
  inversion 1.
  - destruct (Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p2) b) eqn:?; auto.
    apply Globalenvs.Genv.find_funct_ptr_iff in Heqo. congruence.
  - destruct (Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv p2) b) eqn:?; auto.
    apply Globalenvs.Genv.find_funct_ptr_iff in Heqo. rewrite Heqo in H5. inv H5.
    inv H6.
    symmetry in H4.
    apply Globalenvs.Genv.find_funct_ptr_iff in H4. congruence.
Qed.

Lemma Asmgen_fn_stack_requirements_match: forall  mp ap,
    Asmgenproof.match_prog mp ap->
    Stackingproof.fn_stack_requirements mp = fn_stack_requirements ap.
Proof.
  intros.
  unfold fn_stack_requirements.
  unfold Stackingproof.fn_stack_requirements.
  apply Axioms.extensionality. intro i.
  destruct (Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv mp)) eqn:FF.
  exploit Asmgenproof.functions_translated; eauto.
  intros (tf & FF' & TF).
  rewrite FF'.
  unfold Asmgen.transf_fundef in TF.
  unfold transf_partial_fundef in TF.
  destr_in TF. unfold bind in TF. destr_in TF. inv TF.
  unfold Asmgen.transf_function in Heqr. unfold bind in Heqr.
  repeat destr_in Heqr.
  apply Asmgen.transl_function_stacksize. apply Heqr0.
  inv TF. auto.
  eapply match_program_no_more_functions in FF; eauto.
  rewrite FF. auto.
Qed.

Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics (fn_stack_requirements tp) p) (Asm.semantics tp)
  /\ backward_simulation (atomic (Cstrategy.semantics (fn_stack_requirements tp) p)) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Cstrategy.semantics (fn_stack_requirements p22) p) (Asm.semantics p22)).
  {
  eapply compose_forward_simulations.
    eapply SimplExprproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
 eapply compose_forward_simulations. eapply RTLmachproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. eapply Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    replace (fn_stack_requirements p22) with (Stackingproof.fn_stack_requirements p21).
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
    eapply Asmgen_fn_stack_requirements_match; eauto.
  eapply Asmgenproof.transf_program_correct; eassumption.
(*  eapply SSAsmproof.transf_program_correct.
  eapply Asmgenproof.transf_program_unchange_rsp; eauto.
  eapply match_program_no_more_functions; eauto. *) }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces.
  eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (Asm.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics (fn_stack_requirements tp) p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.

(*
Lemma match_prog_wf:
  forall p tp,
    match_prog p tp ->
    AsmFacts.asm_prog_unchange_rsp (Globalenvs.Genv.globalenv tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
  repeat DestructM. subst tp.
  inv M21.
  eapply Asmgenproof.transf_program_unchange_rsp; eauto.
  eapply match_program_no_more_functions; eauto.
Qed.

Theorem c_semantic_preservation_real:
  forall p tp,
  match_prog_real p tp ->
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (RealAsm.semantics tp).
Proof.
  intros.
  unfold match_prog_real in H.
  rewrite compose_passes_app in H.
  fold match_prog in H.
  destruct H as (pi & MP & P).
  simpl in P. destruct P as (p2 & P & EQ). inv EQ.
  apply compose_backward_simulation with (SSAsm.semantics pi).
  apply RealAsm.real_asm_single_events.
  replace (fn_stack_requirements tp) with (fn_stack_requirements pi).
  eapply c_semantic_preservation; eauto.
  exploit RealAsmproof.match_prog_inv; eauto. intro EQ. inv EQ. auto.
  apply RealAsmproof.real_asm_correct'; eauto.
  unfold RealAsmproof.match_prog. auto.
  exploit match_prog_wf; eauto.
  intros (A&B&C). red in A. red. intros.
  red. intros. exploit AsmFacts.in_find_instr; eauto.
  intros [ofs H2]. eapply A; eauto.
Qed.
*)
(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.
(*
Theorem transf_c_program_correct_real:
  forall p tp,
  transf_c_program_real p = OK tp ->
  backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (RealAsm.semantics tp).
Proof.
  intros. apply c_semantic_preservation_real. apply transf_c_program_real_match; auto.
Qed.
*)
(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Csem.semantics (fn_stack_requirements asm_program) c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_c_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply c_semantic_preservation; auto.
Qed.
(*
Theorem separate_transf_c_program_correct_real:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program_real cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Csem.semantics (fn_stack_requirements asm_program) c_program) (RealAsm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_real c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_c_program_real_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_real c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply c_semantic_preservation_real; auto.
Qed.
*)
