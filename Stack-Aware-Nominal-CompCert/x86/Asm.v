(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for IA32 assembly language *)

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.

(** * Abstract syntax *)

(** ** Registers. *)

(** Integer registers. *)

Inductive ireg: Type :=
  | RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0  | XMM1  | XMM2  | XMM3  | XMM4  | XMM5  | XMM6  | XMM7
  | XMM8  | XMM9  | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register. *)

Inductive crbit: Type :=
  | ZF | CF | PF | SF | OF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation SP := RSP (only parsing).

(** ** Instruction set. *)

Definition label := positive.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * Z))
             (const: Z + ident * ptrofs).

(** Testable conditions (for conditional jumps and more). *)

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np.

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions for types:
- [b]: 8 bits
- [w]: 16 bits ("word")
- [l]: 32 bits ("longword")
- [q]: 64 bits ("quadword")
- [d] or [sd]: FP double precision (64 bits)
- [s] or [ss]: FP single precision (32 bits)

  Naming conventions for operands:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (integer) *)
  | Pmovl_ri (rd: ireg) (n: int)
  | Pmovq_ri (rd: ireg) (n: int64)
  | Pmov_rs (rd: ireg) (id: ident)
  | Pmovl_rm (rd: ireg) (a: addrmode)
  | Pmovq_rm (rd: ireg) (a: addrmode)
  | Pmovl_mr (a: addrmode) (rs: ireg)
  | Pmovq_mr (a: addrmode) (rs: ireg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pmovss_fi (rd: freg) (n: float32)   (**r [movss] (single 32-bit float) *)
  | Pmovss_fm (rd: freg) (a: addrmode)
  | Pmovss_mf (a: addrmode) (r1: freg)
  | Pfldl_m (a: addrmode)               (**r [fld] double precision *)
  | Pfstpl_m (a: addrmode)              (**r [fstp] double precision *)
  | Pflds_m (a: addrmode)               (**r [fld] simple precision *)
  | Pfstps_m (a: addrmode)              (**r [fstp] simple precision *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)     (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)     (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)     (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)     (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pmovzl_rr (rd: ireg) (rs: ireg)     (**r [movzl] (32-bit zero-extension) *)
  | Pmovsl_rr (rd: ireg) (rs: ireg)     (**r [movsl] (32-bit sign-extension) *)
  | Pmovls_rr (rd: ireg)                (** 64 to 32 bit conversion (pseudo) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg)  (**r conversion to single float *)
  | Pcvtss2sd_ff (rd: freg) (r1: freg)  (**r conversion to double float *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  | Pcvttss2si_rf (rd: ireg) (r1: freg) (**r single to signed int *)
  | Pcvtsi2ss_fr (rd: freg) (r1: ireg)  (**r signed int to single *)
  | Pcvttsd2sl_rf (rd: ireg) (r1: freg) (**r double to signed long *)
  | Pcvtsl2sd_fr (rd: freg) (r1: ireg)  (**r signed long to double *)
  | Pcvttss2sl_rf (rd: ireg) (r1: freg) (**r single to signed long *)
  | Pcvtsl2ss_fr (rd: freg) (r1: ireg)  (**r signed long to single *)
  (** Integer arithmetic *)
  | Pleal (rd: ireg) (a: addrmode)
  | Pleaq (rd: ireg) (a: addrmode)
  | Pnegl (rd: ireg)
  | Pnegq (rd: ireg)
  | Paddl_ri (rd: ireg) (n: int)
  | Paddq_ri (rd: ireg) (n: int64)
  | Psubl_rr (rd: ireg) (r1: ireg)
  | Psubq_rr (rd: ireg) (r1: ireg)
  | Pimull_rr (rd: ireg) (r1: ireg)
  | Pimulq_rr (rd: ireg) (r1: ireg)
  | Pimull_ri (rd: ireg) (n: int)
  | Pimulq_ri (rd: ireg) (n: int64)
  | Pimull_r (r1: ireg)
  | Pimulq_r (r1: ireg)
  | Pmull_r (r1: ireg)
  | Pmulq_r (r1: ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1: ireg)
  | Pdivq (r1: ireg)
  | Pidivl (r1: ireg)
  | Pidivq (r1: ireg)
  | Pandl_rr (rd: ireg) (r1: ireg)
  | Pandq_rr (rd: ireg) (r1: ireg)
  | Pandl_ri (rd: ireg) (n: int)
  | Pandq_ri (rd: ireg) (n: int64)
  | Porl_rr (rd: ireg) (r1: ireg)
  | Porq_rr (rd: ireg) (r1: ireg)
  | Porl_ri (rd: ireg) (n: int)
  | Porq_ri (rd: ireg) (n: int64)
  | Pxorl_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxorq_r (rd: ireg)
  | Pxorl_rr (rd: ireg) (r1: ireg)
  | Pxorq_rr (rd: ireg) (r1: ireg)
  | Pxorl_ri (rd: ireg) (n: int)
  | Pxorq_ri (rd: ireg) (n: int64)
  | Pnotl (rd: ireg)
  | Pnotq (rd: ireg)
  | Psall_rcl (rd: ireg)
  | Psalq_rcl (rd: ireg)
  | Psall_ri (rd: ireg) (n: int)
  | Psalq_ri (rd: ireg) (n: int)
  | Pshrl_rcl (rd: ireg)
  | Pshrq_rcl (rd: ireg)
  | Pshrl_ri (rd: ireg) (n: int)
  | Pshrq_ri (rd: ireg) (n: int)
  | Psarl_rcl (rd: ireg)
  | Psarq_rcl (rd: ireg)
  | Psarl_ri (rd: ireg) (n: int)
  | Psarq_ri (rd: ireg) (n: int)
  | Pshld_ri (rd: ireg) (r1: ireg) (n: int)
  | Prorl_ri (rd: ireg) (n: int)
  | Prorq_ri (rd: ireg) (n: int)
  | Pcmpl_rr (r1 r2: ireg)
  | Pcmpq_rr (r1 r2: ireg)
  | Pcmpl_ri (r1: ireg) (n: int)
  | Pcmpq_ri (r1: ireg) (n: int64)
  | Ptestl_rr (r1 r2: ireg)
  | Ptestq_rr (r1 r2: ireg)
  | Ptestl_ri (r1: ireg) (n: int)
  | Ptestq_ri (r1: ireg) (n: int64)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  | Padds_ff (rd: freg) (r1: freg)
  | Psubs_ff (rd: freg) (r1: freg)
  | Pmuls_ff (rd: freg) (r1: freg)
  | Pdivs_ff (rd: freg) (r1: freg)
  | Pnegs (rd: freg)
  | Pabss (rd: freg)
  | Pcomiss_ff (r1 r2: freg)
  | Pxorps_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident) (sg: signature)
  | Pjmp_r (r: ireg) (sg: signature)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)   (**r pseudo *)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident) (sg: signature)
  | Pcall_r (r: ireg) (sg: signature)
  | Pret
  (** Saving and restoring registers *)
  | Pmov_rm_a (rd: ireg) (a: addrmode)  (**r like [Pmov_rm], using [Many64] chunk *)
  | Pmov_mr_a (a: addrmode) (rs: ireg)  (**r like [Pmov_mr], using [Many64] chunk *)
  | Pmovsd_fm_a (rd: freg) (a: addrmode) (**r like [Pmovsd_fm], using [Many64] chunk *)
  | Pmovsd_mf_a (a: addrmode) (r1: freg) (**r like [Pmovsd_mf], using [Many64] chunk *)
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: ptrofs)
  | Pbuiltin(ef: external_function)(args: list (builtin_arg preg))(res: builtin_res preg)
  (** Instructions not generated by [Asmgen] -- TO CHECK *)
  | Padcl_ri (rd: ireg) (n: int)
  | Padcl_rr (rd: ireg) (r2: ireg)
  | Paddl_mi (a: addrmode) (n: int)
  | Paddl_rr (rd: ireg) (r2: ireg)
  | Pbsfl (rd: ireg) (r1: ireg)
  | Pbsfq (rd: ireg) (r1: ireg)
  | Pbsrl (rd: ireg) (r1: ireg)
  | Pbsrq (rd: ireg) (r1: ireg)
  | Pbswap64 (rd: ireg)
  | Pbswap32 (rd: ireg)
  | Pbswap16 (rd: ireg)
  | Pcfi_adjust (n: int)
  | Pfmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmadd231 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub132 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub213 (rd: freg) (r2: freg) (r3: freg)
  | Pfnmsub231 (rd: freg) (r2: freg) (r3: freg)
  | Pmaxsd (rd: freg) (r2: freg)
  | Pminsd (rd: freg) (r2: freg)
  | Pmovb_rm (rd: ireg) (a: addrmode)
  | Pmovq_rf (rd: ireg) (r1: freg)
  | Pmovsq_mr  (a: addrmode) (rs: freg)
  | Pmovsq_rm (rd: freg) (a: addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd: ireg) (ad: addrmode)
  | Pnop
  | Prep_movsl
  | Psbbl_rr (rd: ireg) (r2: ireg)
  | Psqrtsd (rd: freg) (r1: freg)
  | Psubl_ri (rd: ireg) (n: int)
  | Psubq_ri (rd: ireg) (n: int64).

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code; fn_stacksize:Z; fn_ofs_link : ptrofs}.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition instr_size (i:instruction) := 1%Z.

Lemma instr_size_repr : forall i, 0<= instr_size i <= Ptrofs.max_unsigned.
Proof.
  intro. unfold instr_size. vm_compute. split; congruence.
Qed.

Lemma instr_size_positive :forall i, 0 < instr_size i.
Proof.
  intro. unfold instr_size. lia.
Qed.
Fixpoint code_size (c:code) : Z :=
  match c with
  |nil => 0
  |i::c' => code_size c' + instr_size i
  end.

Lemma code_size_non_neg: forall c, 0 <= code_size c.
Proof.
  intros. induction c; simpl. lia. unfold instr_size. lia.
Qed.

(** * Operational semantics *)

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. decide equality. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

Fixpoint no_rsp_pair (b: rpair preg) :=
  match b with
  | One r => r <> RSP
  | Twolong hi lo => hi <> RSP /\ lo <> RSP
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Definition aligned_fsz (sz:Z) := align (Z.max 0 sz) 8.

Definition check_topframe (sz:Z)(astack:stackadt) : bool :=
  match astack with
    |nil => false
    |top::tl => match top with
                |fr::nil => if (zeq sz (frame_size fr)) then true else false
                |_ => false
              end
  end.

Fixpoint sp_of_stack' (s:stree) : list fid * path :=
  match s with
   |Node fid bl l None => (fid::nil,nil)
   |Node fid bl l (Some s') =>
    let (lf',path') := sp_of_stack' s' in let idx := length l in
    (lf'++(fid::nil),idx::path')
  end.

Lemma sp_of_stack'_nonempty : forall s lf p, sp_of_stack' s= (lf,p) -> lf <> nil.
Proof.
  intros. destruct s. destruct o; simpl in H. destr_in H; inv H.
  intro. destruct l1 in H; inv H. inv H. congruence .
Qed.

(* we have to ignore the root node*)
Definition sp_of_stack (s:stree) : list fid * path :=
  let (lf,path) := (sp_of_stack' s) in (removelast lf,path).

Definition parent_sp_stree (st:stree) : val :=
  let (lf,path) := sp_of_stack st in
  match (lf,path) with
    |(f1::((Some id)::tl), _::(_::_)) =>
     Vptr (Stack (Some id) (removelast path) 1%positive) Ptrofs.zero
    |_ => Vptr (Stack None nil 1) Ptrofs.zero
  end.

Definition top_sp_stree (st:stree) : val :=
  let (lf,path) := sp_of_stack st in
  match (lf,path) with
    | (((Some id)::tl), (_::_)) =>
     Vptr (Stack (Some id) path 1%positive) Ptrofs.zero
    |_ => Vptr (Stack None nil 1) Ptrofs.zero
  end.

Lemma sp_of_stack_pspnull : forall st fid idx,
    sp_of_stack st = (fid::nil,idx::nil) -> parent_sp_stree st = Vptr (Stack None nil 1) Ptrofs.zero.
Proof.
  intros. unfold parent_sp_stree. rewrite H. auto.
Qed.

Lemma append_nil_right : forall A (l:list A),
    l++nil = l.
Proof.
  induction l. auto. simpl. congruence.
Qed.

Lemma sp_of_stack_pspsome : forall st f1 lf path idx2 idx1 id,
    sp_of_stack st = (f1::(Some id)::lf, (path++(idx2::nil))++(idx1::nil)) ->
    parent_sp_stree st = Vptr (Stack (Some id) (path++(idx2::nil)) 1%positive) Ptrofs.zero.
Proof.
  intros. unfold parent_sp_stree. rewrite H. simpl.
  destruct path. auto. destruct path. auto. rewrite removelast_app. simpl.
  rewrite append_nil_right. auto. congruence.
Qed.

Lemma sp_of_stack_tspsome : forall st id lf path idx,
    sp_of_stack st = ((Some id)::lf,path++(idx::nil)) ->
    top_sp_stree st = Vptr (Stack (Some id) (path++(idx::nil)) 1%positive) Ptrofs.zero.
Proof.
  intros. unfold top_sp_stree. rewrite H. simpl.
  destr. destruct path; inv Heql.
Qed.

Lemma sp_of_stack_return' : forall st st' p' fid lf path idx root,
    return_stree st = Some (st',p') ->
    sp_of_stack' st = (fid::lf++(root::nil),path++(idx::nil)) ->
    sp_of_stack' st' = (lf++(root::nil),path).
Proof.
  induction st. intros. destruct st. destruct o.
  - destruct st'. destruct s. destruct o0.
    + remember (Node f1 l3 l4 (Some s)) as st1.
      simpl in H0. destr_in H0. destr_in H0. subst p.
      simpl in H1. destr_in H1. inv H1.
      destruct l5. inv H3. destruct lf; inv H5.
      assert (l5<>nil).
      {destruct l5.
      simpl in Heqp. destr_in Heqp. destruct s. destruct o0; simpl in Heqp1.
      -- destr_in Heqp1. inv Heqp1. destruct l8; inv Heqp. simpl in H5. destruct l8; inv H5.
      -- inv Heqp1. inv Heqp.
      -- congruence.
      }
      apply exists_last in H1. destruct H1 as (l' & root' & H1). subst.
      assert (p<> nil).
      {
        simpl in Heqp. destr_in Heqp.
      }
      apply exists_last in H1. destruct H1 as (path0 & idx' & H1). subst.
      exploit H; eauto. simpl. auto. intro.
      inv H0. simpl. rewrite H1.
      assert (removelast ((Datatypes.length l2 :: path0) ++ idx'::nil) = removelast (path++idx::nil)).
      setoid_rewrite H4. auto.
      rewrite removelast_app in H0. simpl in H0. rewrite removelast_app in H0. simpl in H0.
      repeat rewrite append_nil_right in H0. subst.
      assert (tl ((f2::l'++root'::nil)++f0::nil) = tl (fid::lf++root::nil)).
      setoid_rewrite H3. auto. simpl in H0. rewrite H0. auto. congruence. congruence.
      rewrite Heqst1 in Heqo0. inv Heqo0. repeat destr_in H3.
    + simpl in H1. simpl in H0. inv H0.
      simpl in *.  inv H1. destruct path; inv H4. auto.
      destruct path; inv H2.
  - inv H1. destruct lf; inv H4.
Qed.

Lemma sp_of_stack_return : forall m1 m2 fid lf path idx,
    Mem.return_frame m1 = Some m2 ->
    sp_of_stack (Mem.stack (Mem.support m1)) = (fid::lf,path++(idx::nil)) ->
    sp_of_stack (Mem.stack (Mem.support m2)) = (lf,path).
Proof.
  intros. apply Mem.support_return_frame in H. unfold Mem.sup_return_frame in H.
  destr_in H. destr_in H. unfold sp_of_stack in *. destr_in H0. inv H0.
  destruct l. inv H2. assert (l<>nil).
  destruct (Mem.stack (Mem.support m1)). destruct o.
  simpl in Heqp1. destr_in Heqp1. inv Heqp1. apply sp_of_stack'_nonempty in Heqp.
  destruct l2. congruence. inv H1. intro. destruct l2; inv H0.
  inv Heqo.
  apply exists_last in H0. destruct H0 as (l' & idx' & H0). subst.
  exploit sp_of_stack_return'; eauto. intro. inv H. simpl. rewrite H0.
  simpl in H2. destr_in H2. inv H2. auto.
Qed.

Lemma sp_of_stack_alloc' : forall st st' st'' path path0 path1 f lf pos id root,
    next_stree st id = (st',path) ->
    next_block_stree st' = (f,pos,path0,st'') ->
    sp_of_stack' st = (lf++root::nil,path1) ->
    exists idx,
    sp_of_stack' st'' = (f::lf++root::nil,path0) /\ path0 = path1 ++ (idx::nil).
Proof.
  induction st. intros. destruct st. destruct o.
  - simpl in H0. destr_in H0. inv H0. simpl in H1. repeat destr_in H1.
    simpl in H2. destr_in H2.
    apply sp_of_stack'_nonempty in Heqp1 as H0.
    apply exists_last in H0. destruct H0 as (l' & a & H0). subst.
    exploit H; eauto. simpl. auto.
    intros (idx & A & B). exists idx. split. simpl. rewrite A.
    inv H2. auto. inv H2. auto.
  - simpl in H0. inv H0. simpl in H1. inv H1. simpl in H2. inv H2. simpl.
    exists (length l0). auto.
Qed.

Lemma sp_of_stack_alloc : forall m1 m2 m3 id path lo hi b lf path',
    Mem.alloc_frame m1 id = (m2,path) ->
    Mem.alloc m2 lo hi = (m3,b) ->
    sp_of_stack (Mem.stack (Mem.support m1)) = (lf,path') ->
    exists idx, b = Stack (Some id) (path'++(idx::nil)) 1%positive /\
    sp_of_stack (Mem.stack (Mem.support m3)) = ((Some id)::lf,path'++(idx::nil)).
Proof.
  intros.
  exploit Mem.alloc_frame_alloc; eauto. intro.
  apply Mem.path_alloc_frame in H as H'. unfold Mem.sup_npath in H'. unfold npath in H'.
  apply Mem.support_alloc_frame in H. unfold Mem.sup_incr_frame in H.
  destr_in H.
  apply Mem.support_alloc in H0. unfold Mem.sup_incr in H0. destr_in H0.
  rewrite H in Heqp0. simpl in Heqp0. destruct p0. destruct p0.
  unfold sp_of_stack in *. destr_in H1.
  apply sp_of_stack'_nonempty in Heqp2 as H3.
  edestruct (exists_last H3) as (a & l' & H4). subst.
  exploit sp_of_stack_alloc'; eauto. intros (idx & A& B).
  exploit next_stree_next_block_stree; eauto. intros (X & Y & Z).
  subst.
  exists idx. split. inv H1. auto.
  rewrite H0. simpl. rewrite A. simpl. inv H1. destr.
Qed.

(* external call will not change the active stack frames*)
Axiom sp_of_stack_external : forall m1 m2 ge ef vargs t vres,
      external_call ef ge vargs m1 t vres m2 ->
      sp_of_stack (Mem.stack (Mem.support m2)) = sp_of_stack (Mem.stack (Mem.support m1)).

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Lemma label_pos_rng:
  forall lbl c pos z,
    label_pos lbl pos c = Some z ->
    0 <= pos ->
    0 <= z - pos <= code_size c.
Proof.
  induction c; simpl; intros; eauto. congruence. repeat destr_in H.
  generalize (code_size_non_neg c) (instr_size_positive a); lia.
  apply IHc in H2.
  generalize (instr_size_positive a); lia.
  generalize (instr_size_positive a); lia.
Qed.

Lemma label_pos_repr:
  forall lbl c pos z,
    code_size c + pos <= Ptrofs.max_unsigned ->
    0 <= pos ->
    label_pos lbl pos c = Some z ->
    Ptrofs.unsigned (Ptrofs.repr (z - pos)) = z - pos.
Proof.
  intros.
  apply Ptrofs.unsigned_repr.
  generalize (label_pos_rng _ _ _ _ H1 H0). lia.
Qed.

Lemma find_instr_ofs_pos:
  forall c o i,
    find_instr o c = Some i ->
    0 <= o.
Proof.
  induction c; simpl; intros; repeat destr_in H.
  lia. apply IHc in H1. generalize (instr_size_positive a); lia.
Qed.

Lemma label_pos_spec:
  forall lbl c pos z,
    code_size c + pos <= Ptrofs.max_unsigned ->
    0 <= pos ->
    label_pos lbl pos c = Some z ->
    find_instr ((z - pos) - instr_size (Plabel lbl)) c = Some (Plabel lbl).
Proof.
  unfold instr_size.
  induction c; simpl; intros; repeat destr_in H1.
  destruct a; simpl in Heqb; try congruence. repeat destr_in Heqb.
  apply pred_dec_true. unfold instr_size. lia.
  eapply IHc in H3. 3: lia. 2: generalize (instr_size_positive a); lia.
  generalize (find_instr_ofs_pos _ _ _ H3). intro.
  rewrite pred_dec_false. 2: generalize (instr_size_positive a); lia.
  rewrite <- H3. f_equal. lia.
Qed.

Variable ge: genv.

(** Evaluating an addressing mode *)

Definition eval_addrmode32 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.add  (match base with
             | None => Vint Int.zero
             | Some r => rs r
            end)
  (Val.add (match ofs with
             | None => Vint Int.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mul (rs r) (Vint (Int.repr sc))
             end)
           (match const with
            | inl ofs => Vint (Int.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode64 (a: addrmode) (rs: regset) : val :=
  let '(Addrmode base ofs const) := a in
  Val.addl (match base with
             | None => Vlong Int64.zero
             | Some r => rs r
            end)
  (Val.addl (match ofs with
             | None => Vlong Int64.zero
             | Some(r, sc) =>
                if zeq sc 1
                then rs r
                else Val.mull (rs r) (Vlong (Int64.repr sc))
             end)
           (match const with
            | inl ofs => Vlong (Int64.repr ofs)
            | inr(id, ofs) => Genv.symbol_address ge id ofs
            end)).

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  if Archi.ptr64 then eval_addrmode64 a rs else eval_addrmode32 a rs.

(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SF = 1 if x - y is negative, 0 if x - y is positive
-       OF = 1 if x - y overflows (signed), 0 if not
-       PF is undefined
*)

Definition compare_ints (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.cmpu (Mem.valid_pointer m) Ceq x y)
     #CF  <- (Val.cmpu (Mem.valid_pointer m) Clt x y)
     #SF  <- (Val.negative (Val.sub x y))
     #OF  <- (Val.sub_overflow x y)
     #PF  <- Vundef.

Definition compare_longs (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq x y))
     #CF  <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt x y))
     #SF  <- (Val.negativel (Val.subl x y))
     #OF  <- (Val.subl_overflow x y)
     #PF  <- Vundef.

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y and ordered
-       CF = 1 if x<y or unordered, 0 if x>=y.
-       PF = 1 if unordered, 0 if ordered.
-       SF and 0F are undefined
*)

Definition compare_floats (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vfloat x, Vfloat y =>
      rs #ZF  <- (Val.of_bool (Float.cmp Ceq x y || negb (Float.ordered x y)))
         #CF  <- (Val.of_bool (negb (Float.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float.ordered x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

Definition compare_floats32 (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vsingle x, Vsingle y =>
      rs #ZF  <- (Val.of_bool (Float32.cmp Ceq x y || negb (Float32.ordered x y)))
         #CF  <- (Val.of_bool (negb (Float32.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float32.ordered x y)))
         #SF  <- Vundef
         #OF  <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | Cond_e =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_ne =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_b =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_be =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ae =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_a =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_l =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
      | _, _ => None
      end
  | Cond_le =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
      | _, _, _ => None
      end
  | Cond_ge =>
      match rs OF, rs SF with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
      | _, _ => None
      end
  | Cond_g =>
      match rs OF, rs SF, rs ZF with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
      | _, _, _ => None
      end
  | Cond_p =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_np =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition nextinstr_nf (rs: regset) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs =>
        match Genv.find_funct_ptr ge b with
        | Some _ => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
        | None => Stuck
        end
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs)) m'
  | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Inductive is_call: instruction -> Prop :=
| is_calls_intro:
    forall i sg,
      is_call (Pcall_s i sg)
| is_callr_intro:
    forall r sg,
      is_call (Pcall_r r sg).

Lemma is_call_dec:
  forall i,
    {is_call i} + {~ is_call i}.
Proof.
  destruct i; try now (right; intro A; inv A).
  left; econstructor; eauto.
  left; econstructor; eauto.
Qed.

Fixpoint offsets_after_call (c: code) (p: Z) : list Z :=
  match c with
    nil => nil
  | i::c => let r := offsets_after_call c (p + instr_size i) in
           if is_call_dec i then (p+instr_size i)::r
           else r
  end.

Definition is_after_call (f: fundef) (o: Z) : Prop :=
  match f with
    Internal f => In o (offsets_after_call (fn_code f) 0)
  | External ef => False
  end.

Definition check_is_after_call f o : {is_after_call f o} + {~ is_after_call f o}.
Proof.
  unfold is_after_call.
  destruct f; auto.
  apply In_dec. apply zeq.
Qed.

Definition ra_after_call (ge: Genv.t fundef unit) v:=
  v <> Vundef /\ forall b o,
    v = Vptr b o ->
    forall f,
      Genv.find_funct_ptr ge b = Some f ->
      is_after_call f (Ptrofs.unsigned o).

Definition check_ra_after_call (ge': Genv.t fundef unit) v:
  {ra_after_call ge' v} + { ~ ra_after_call ge' v}.
Proof.
  unfold ra_after_call.
  destruct v; try now (left; split; intros; congruence).
  right; intuition congruence.
  destruct (Genv.find_funct_ptr ge' b) eqn:FFP.
  2: left; split; [congruence|]; intros b0 o A; inv A; rewrite FFP; congruence.
  destruct (check_is_after_call f (Ptrofs.unsigned i)).
  left. split. congruence. intros b0 o A; inv A; rewrite FFP; congruence.
  right; intros (B & A); specialize (A _ _ eq_refl _ FFP). congruence.
Defined.

(*ra from mem shound not be Vundef*)
Definition loadvv chunk m v : option val:=
  match Mem.loadv chunk m v with
  | None | Some Vundef => None
  | Some v => Some v
  end.

Lemma loadv_loadvv :
  forall chunk m vp v,
    Mem.loadv chunk m vp = Some v -> v <> Vundef ->
    loadvv chunk m vp = Some v.
Proof.
  intros.
  unfold loadvv. rewrite H. destruct v; eauto. congruence.
Qed.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n))) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n))) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero))) m
  | Pmovl_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmovq_rm rd a =>
      exec_load Mint64 m a rs rd
  | Pmovl_mr a r1 =>
      exec_store Mint32 m a rs r1 nil
  | Pmovq_mr a r1 =>
      exec_store Mint64 m a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n))) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil)
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 a rs))) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n)))) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1))) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1))) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n)))) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63))))) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1))) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n)))) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1))) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n)))) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero))) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1))) m
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n)))) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd))) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX))) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX))) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n)))) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX))) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX))) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n)))) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX))) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX))) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n)))) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n)))) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m)) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m)) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m)) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m)) m
  | Pcmov c rd r1 =>
      let v :=
        match eval_testcond c rs with
        | Some b => if b then rs#r1 else rs#rd
        | None   => Vundef
      end in
      Next (nextinstr (rs#rd <- v)) m
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
    let addr := Genv.symbol_address ge id Ptrofs.zero in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#PC <- addr) m
    | _ => Stuck
    end
  | Pjmp_r r sg =>
    let addr := (rs r) in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#PC <- addr) m
    | _ => Stuck
    end
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
    let addr := Genv.symbol_address ge id Ptrofs.zero in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- addr) m
    | _ => Stuck
    end
  | Pcall_r r sg =>
    let addr := (rs r) in
    match Genv.find_funct ge addr with
    | Some _ =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- addr) m
    | _ => Stuck
    end
  | Pret =>
    if check_ra_after_call ge (rs#RA) then Next (rs#PC <- (rs#RA) #RA <- Vundef) m else Stuck
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pallocframe sz ofs_ra ofs_link =>
    if zle 0 sz then
    match rs # PC with
    |Vptr (Global id) _
     =>
     let (m0,path) := Mem.alloc_frame m id in
     let (m1, stk) := Mem.alloc m0 0 sz in
     match Mem.record_frame (Mem.push_stage m1) (Memory.mk_frame sz) with
     |None => Stuck
     |Some m2 =>
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
      | None => Stuck
      | Some m3 =>
        match Mem.storev Mptr m3 (Val.offset_ptr sp ofs_link) rs#RSP with
        | None => Stuck
        | Some m4 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m4
        end
      end
     end
    |_ => Stuck
    end else Stuck
  | Pfreeframe sz ofs_ra ofs_link =>
    if zle 0 sz then
      match loadvv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
          | None => Stuck
          | Some sp =>
              match rs#RSP with
              | Vptr stk ofs =>
                  if check_topframe sz (Mem.astack (Mem.support m)) then
                  if Val.eq sp (parent_sp_stree (Mem.stack (Mem.support m))) then
                  if Val.eq (Vptr stk ofs) (top_sp_stree (Mem.stack (Mem.support m))) then
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' =>
                    match Mem.return_frame m' with
                    | None => Stuck
                    | Some m'' =>
                      match Mem.pop_stage m'' with
                        | None => Stuck
                        | Some m''' =>
                        Next (nextinstr (rs#RSP <- sp #RA <- ra)) m'''
                      end
                    end
                  end else Stuck else Stuck else Stuck
              | _ => Stuck
              end
          end
      end else Stuck
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pcfi_adjust _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovq_rf _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Pnop
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
  | Psubl_ri _ _
  | Psubq_ri _ _ => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the Asm view.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | AX => IR RAX
  | BX => IR RBX
  | CX => IR RCX
  | DX => IR RDX
  | SI => IR RSI
  | DI => IR RDI
  | BP => IR RBP
  | Machregs.R8 => IR R8
  | Machregs.R9 => IR R9
  | Machregs.R10 => IR R10
  | Machregs.R11 => IR R11
  | Machregs.R12 => IR R12
  | Machregs.R13 => IR R13
  | Machregs.R14 => IR R14
  | Machregs.R15 => IR R15
  | X0 => FR XMM0
  | X1 => FR XMM1
  | X2 => FR XMM2
  | X3 => FR XMM3
  | X4 => FR XMM4
  | X5 => FR XMM5
  | X6 => FR XMM6
  | X7 => FR XMM7
  | X8 => FR XMM8
  | X9 => FR XMM9
  | X10 => FR XMM10
  | X11 => FR XMM11
  | X12 => FR XMM12
  | X13 => FR XMM13
  | X14 => FR XMM14
  | X15 => FR XMM15
  | FP0 => ST0
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Fixpoint in_builtin_res (b:builtin_res preg) (r:preg) :=
  match b with
    |BR b => b =r
    |BR_none => False
    |BR_splitlong hi lo => in_builtin_res hi r \/ in_builtin_res lo r
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ in_builtin_res res RSP ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef),
      external_call ef ge args m t res m' ->
      no_rsp_pair (loc_external_result (ef_sig ef)) ->
      ra_after_call ge (rs#RA)->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))
              #PC <- (rs RA)
              #RA <- Vundef
      ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 m1 b0 bmain,
      Genv.init_mem p = Some m0 ->
      Mem.alloc m0 0 0 = (m1,b0) ->
      let ge := Genv.globalenv p in
      Genv.find_symbol ge p.(prog_main) = Some bmain ->
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Vptr bmain Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- (Vptr (Stack None nil 1) Ptrofs.zero) in
      initial_state p (State rs0 m1).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H12. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H4. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros; inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. subst ge. subst ge0. rewrite H3 in H5. inv H5. reflexivity.
  congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  | RA => false
  end.


Definition instr_invalid (i: instruction) :=
  match i with
  | Pjmp_l _
  | Pjcc _ _
  | Pjcc2 _ _ _
  | Pjmptbl _ _
  | Pallocframe _ _ _
  | Pfreeframe _ _ _ => True
  | _ => False
  end.

Definition instr_valid i := ~instr_invalid i.

Lemma instr_invalid_dec: forall i, {instr_invalid i} + {~instr_invalid i}.
Proof.
  destruct i; cbn; auto.
Qed.

Lemma instr_valid_dec: forall i, {instr_valid i} + {~instr_valid i}.
Proof.
  unfold instr_valid.
  destruct i; cbn; auto.
Qed.

Definition def_instrs_valid (def: option (globdef fundef unit)) :=
  match def with
  | None => True
  | Some (Gvar v) => True
  | Some (Gfun f) =>
    match f with
    | External _ => True
    | Internal f =>  Forall instr_valid (fn_code f)
    end
  end.

Lemma def_instrs_valid_dec:
  forall def, {def_instrs_valid def} + {~def_instrs_valid def}.
Proof.
  destruct def. destruct g.
  - destruct f.
    + simpl. apply Forall_dec. apply instr_valid_dec.
    + simpl. auto.
  - simpl. auto.
  - simpl. auto.
Qed.
