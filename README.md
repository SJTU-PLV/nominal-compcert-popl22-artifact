# Verified Compilation of C Programs with a Nominal Memory Model (Artifact for POPL 2022)

## Overview

This artifact consists of a series of extensions to CompCert (v3.8)
based on a nominal memory model, as follows:

1. [Nominal CompCert](Nominal-CompCert)
2. [Nominal CompCert with Structured Memory Space](Nominal-CompCert-Struct-Memspace)
3. [Stack-Aware Nominal CompCert](Stack-Aware-Nominal-CompCert)
4. [Multi-Stack CompCert](Multi-Stack-CompCert)

The complete source code of each extension can be found in a
corresponding top-level directory (we have included a copy of CompCert
v3.8 for comparison and reference). The artifact accompanies the
following paper:

> [*Verified Compilation of C Programs with a Nominal Memory
  Model*](paper/nominalcompcert.pdf). Yuting Wang, Ling Zhang, Zhong
  Shao and Jeremie Koenig

As described in the paper, these extensions are developed
incrementally, with Nominal CompCert as the basic extension of
CompCert based on the nominal memory model, and Multi-Stack CompCert as
the most sophisticated extension that combines all the features
introduced in the paper. Moreover, they correspond to the main claims
we make in Section 1.3 of the paper, as follows:

1. The nominal memory model is a natural extension of the block-based
   memory model. It enables flexible formalization of block ids and
   eliminates global assumptions on memory space. These claims are
   justified by the realization of nominal memory model in Nominal
   CompCert.

2. Nominal CompCert is an extension with the full compilation chain of
   CompCert verified and a general framework for verified compilation
   of C programs. This is justified by the implementation of Nominal
   CompCert.

3. We developed an extension of Nominal CompCert that enables
   intuitive reasoning of compiler transformations on partial
   memory. This is justified by Nominal CompCert with Structured
   Memory Space.

4. We developed extensions of Nominal CompCert that enable modular
   reasoning about open programs with contextual memory. This is
   justified by Stack-Aware Nominal CompCert and Multi-Stack CompCert.

5. The above developments are lightweight and easy to adopt. This can
   be observed by comparing our extensions with CompCert v3.8.

We shall delve into the details of these extensions later.


## Compilation and Testing

### Prerequisites

This artifact is based on CompCert v3.8 and needs Coq v8.12 to
compile.

- If you are using the VM, you are set. All the required software have
already been installed on the virtual machine.

- If you prefer to compile the source code on your own computer, then
we suggest you install the prerequisites via
[opam](https://opam.ocaml.org/) and follow the standard installation
steps in [the user's manual of
CompCert](https://compcert.org/man/index.html) to compiler the source
code.

### Configuring and compiling the code

We assume you are testing the artifact on Ubuntu LTS 20.04 (the OS of
the virtual machine). To compile the source code of each extension,
enter its directory, run the following commands:

```
./configure x86_64-linux
make
```

The compilation should start and terminate successfully. Currently,
the artifact only works for the x86 back-end because Stack-Awareness
is only implemented for x86.

For each extension, we have tested its compilation by running the
command `make -j4` on the VM with 4GB virtual memory and 4 CPU
cores. The VM in turn runs on a host machine with Intel i7-8550U and
8GB memory. A single run takes about 15 minutes.

### Navigating the proofs

After that,
you can navigate the source code by using emacs. For example, running

```
emacs common/Memory.v
```

opens the emacs window in proof-general mode for browsing the file
`common/Memory.v`. The commands for navigating the Coq proof scripts
can be found at [here](https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/).

You can also compile the source code into html files for better
presentation. Simply run the following command (which needs
`coq2html` which has been installed on the VM)

```
make documentation
```

Then, the html versions of source code can be found at `doc/html`.

### Checking the test cases

To check that our CompCert extensions work for compiling C programs,
you can run the test cases in the `test` directory, as follows:

```
make
make test
```

With the previous hardware setup, a single run takes about 2 minutes
except for the "Interpreted tests" for Nominal CompCert which take
about 15 minutes. This is because `fresh_block` in Nominal CompCert
traverses the whole support and is invoked every time a new block is
allocated. The interpretation of these invocations in Coq takes a
long time.

## Extension 1: Nominal CompCert

In the remaining sections, we present the details of each extension
and show their correspondence to the discussion in the paper. We first
discuss the nominal memory model and Nominal CompCert, which are
implemented in the directory [`Nominal-CompCert`](Nominal-CompCert)
and correspond to the contents in Section 3 of the paper.

### Nominal memory model

The nominal memory model is introduced Section 3.2. Its constituents
are listed as follows:

- (Lines 442-445) The interface for nominal block ids `BLOCK` is defined by the Coq module type
  `BLOCK` in [`common/Values.v`](Nominal-CompCert/common/Values.v).

- (Lines 491-493) The instantiation of `BLOCK` with positive ids is defined by the Coq
  module `Block` in [`common/Values.v`](Nominal-CompCert/common/Values.v).

- (Lines 447-458) The interface for supports `SUP` is defined by the module type `SUP` in
  [`common/Memtype.v`](Nominal-CompCert/common/Memtype.v).

- (Lines 495-499) The instantiation of supports as a list of block ids is defined by
  the module `Sup` in [`common/Memory.v`](Nominal-CompCert/common/Memory.v).

- (Lines 525-535) The updated memory state `mem` is defined in
  [`common/Memory.v`](Nominal-CompCert/common/Memory.v) with a new
  field `support:sup`.  The updated definition of `valid_block` can
  also be found in this file. The basic properties of the memory model
  have been reproved with these changes.


### Nominal CompCert

Nominal CompCert is introduced in Section 3.3. As described in the
paper, Nominal CompCert updates the full compilation chain of CompCert
with the nominal memory model. Besides the generalized memory model we
have discussed above, the changes w.r.t. CompCert are mainly about the
semantics of languages and updates of proofs. These changes are not
very big and listed as follows:

- (Lines 542-545) One main difference is that next blocks are replaced
  by supports along with the related properties. For instance, in
  [`cfrontend/Cminorgenproof.v`](CompCert-3.8/cfrontend/Cminorgenproof.v)
  in CompCert v3.8, there was an old lemma stating that next block is
  not changed by the operation `free_list`:

  ```
  Lemma nextblock_freelist:
    forall fbl m m',
    Mem.free_list m fbl = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
  ```

  It is generalized to the following theorem about support in
  [`cfrontend/Cminorgenproof.v`](Nominal-CompCert/cfrontend/Cminorgenproof.v)
  in Nominal CompCert:

  ```
  Lemma support_freelist:
    forall fbl m m',
      Mem.free_list m fbl = Some m' ->
      Mem.support m' = Mem.support m.
  ```

  There exists many other small changes with the same nature; we
  elide a discussion of them.

- (Lines 546-552) The changes to valid blocks is demonstrated in
  [`backend/Inliningproof.v`](Nominal-CompCert/backend/Inliningproof.v). Previously,
  the invariant `match_stacks_cons` in [CompCert
  v3.8](CompCert-3.8/backend/Inliningproof.v) assumes:

  ```
  (BELOW: Plt sp' bound)
  ```

  which guarantees that `sp'` is a valid block.  In [Nominal
  CompCert](Nominal-CompCert/backend/Inliningproof.v), the next block
  `bound` is changed to `support` and the above proposition is broken
  into two:

  ```
  (SPS': sp' = fresh_block sps')
  ...
  (BELOW: Mem.sup_include (sup_add sp' sps') support)
  ```

  We elide a discussion of similar changes.

- (Theorem 3.1) The proofs are updated accordingly with the above
  changes. The final correctness theorem is proved in
  [`driver/Compiler.v`](Nominal-CompCert/driver/Compiler.v) as
  follows:

  ```
  Theorem transf_c_program_correct:
    forall p tp,
    transf_c_program p = OK tp ->
    backward_simulation (Csem.semantics p) (Asm.semantics tp).
  ```

### Instantiation of Nominal CompCert

As described in Section 3.4, there is *zero immediate overhead* to introduce
instantiations of block ids and supports. One can provide different implementations
for `Module Block` in  [`common/Values.v`](Nominal-CompCert/common/Values.v) and
`Module Sup` in [`common/Memory.v`](Nominal-CompCert/common/Memory.v). As long as these
implementations satisfy the corresponding interfaces (`Module Block <: BLOCK` and
`Module Sup <: SUP`), the entire proof of Nominal CompCert still holds.


## Extension 2: Nominal CompCert with Structured Memory Space

This extension is implemented in the directory
[`Nominal-CompCert-Struct-Memspace`](Nominal-CompCert-Struct-Memspace)
and corresponds to the contents in Section 4 and 5.1.

### Nominal memory model with structured space

This instantiation of nominal memory model is introduced in Section
4.2. Its constituents are described as follows:

- (Section 4.2.1) `fid`, `path` and the module `Block` are defined in
  [`common/Values.v`](Nominal-CompCert-Struct-Memspace/common/Values.v).

- (Section 4.2.2) `stree` is defined in
  [`common/Memory.v`](Nominal-CompCert-Struct-Memspace/common/Memory.v),
  together with its operations `next_stree`, `next_block_stree`,
  `return_stree` and `stree_in` and their properties. A well-founded
  induction principle `stree_ind` is also established for induction
  over strees.

- (Section 4.2.3) The formalization of support, i.e., module `Sup`, is
  defined in
  [`common/Memory.v`](Nominal-CompCert-Struct-Memspace/common/Memory.v).

- (Section 4.2.4) The memory operations `alloc_glob`, `alloc_frame`,
  `return_frame` and `alloc_block` are defined in
  [`common/Memory.v`](Nominal-CompCert-Struct-Memspace/common/Memory.v).
  Essential properties about these operations are also proved there.

### Nominal CompCert with structured memory space

This extension is introduced in Section 4.3. The updates to semantics
of CompCert's languages are as follows:

- (Lines 828-830) Originally, the allocation global variables in the
 function `alloc_global` in
 [`common/Globalenvs.v`](CompCert-3.8/common/Globalenvs.v) is done by
 using the `alloc` method. In this extension, `alloc_glob` is used
 instead in [this
 extension](Nominal-CompCert-Struct-Memspace/common/Globalenvs.v) .

- (Line 831) `alloc_frame` and `return_frame` are added to function
  calls and returns. For example, in Cminor, the small-step transition
  is changed from [the original
  definition](CompCert-3.8/backend/Cminor.v):

  ```
  Inductive step: state -> trace -> state -> Prop :=
  ...
  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m')
  ...
  | step_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m')
  ...
  ```

  to [the new one](Nominal-CompCert-Struct-Memspace/backend/Cminor.v):

  ```
  Inductive step: state -> trace -> state -> Prop :=
  ...
  | step_return_0: forall f k sp e m m' m'',
    Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
    (* return_frame *)
    Mem.return_frame m' = Some m'' ->
    step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
      E0 (Returnstate Vundef (call_cont k) m'')
  ...
  | step_internal_function: forall f vargs k m m' m'' sp e path id,
    (* alloc_frame *)
    Mem.alloc_frame m id = (m', path) ->
    Mem.alloc m' 0 f.(fn_stackspace) = (m'', sp) ->
    set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
    step (Callstate (Internal f) vargs k m id)
      E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m'')
  ...
  ```

- (Line 832) In our artifact, `alloc` is updated to have the same
  implementation as `alloc_block`. Therefore, we have reused the
  `alloc` method for allocation of stack blocks.

- (Line 841-847) With the above changes, we are able to update the
  complete proofs of CompCert, the final correctness theorem is again
  found at `transf_c_program_correct` in
  [`driver/Compiler.v`](Nominal-CompCert-Struct-Memspace/driver/Compiler.v).

### Intuitive proofs for partial memory transformation

This corresponds to the discussion in Section 4.4. We have updated
the proofs for `SimplLocals`, `Cminorgen`, `Unusedglob` and
`Stacking` to use structural memory injections. They are formalized
in 
[`cfrontend/SimplLocalsproof.v`](Nominal-CompCert-Struct-Memspace/cfrontend/SimplLocalsproof.v), 
[`cfrontend/Cminorgenproof.v`](Nominal-CompCert-Struct-Memspace/cfrontend/Cminorgenproof.v),
[`backend/Unusedglobproof.v`](Nominal-CompCert-Struct-Memspace/backend/Unusedglobproof.v) and 
[`backend/Stackingproof.v`](Nominal-CompCert-Struct-Memspace/backend/Stackingproof.v).

- (Section 4.4.1) For each pass, its structural memory injection is
  defined as the function `struct_meminj`. The implementation of
  `struct_meminj` varies for different passes. For example,
  `struct_meminj` for `Unusedglobal` (lines 834-839) is defined in
  [`backend/Unusedglobproof.v`](Nominal-CompCert-Struct-Memspace/backend/Unusedglobproof.v) 
  as follows:
 
  ```
  Definition check_block (s:sup): block -> bool :=
    fun b =>
      match b with
      |Global id => match Genv.find_symbol tge id with
                     |Some _ => true | None => false
                   end
      |Stack _ _ _ => if Mem.sup_dec b s then true else false
      end.
  
  Definition struct_meminj (s:sup) :=
    fun b => if check_block s b then Some (b,0) else None.
  ```

  and `struct_meminj` for `Cminorgen` (lines 895-900) is defined in
  [`cfrontend/Cminorgenproof.v`](Nominal-CompCert-Struct-Memspace/cfrontend/Cminorgenproof.v)
   as follows:

  ```
  Definition unchecked_meminj : meminj :=
    fun b => match b with
      |Stack (Some id) path pos =>
        match find_frame_offset id pos with
          | Some o =>
        Some ((Stack (Some id) path 1),o)
          | None => None
        end
      |_ => Some (b,0)
      end.
  
  Definition struct_meminj (s:sup) : meminj :=
    fun b => if Mem.sup_dec b s then
             unchecked_meminj b else None.
  ```

- (Section 4.4.2 and 4.4.3) With the structured memory injection, we
  are able to simplify the reasoning about stack memory. For example,
  in
  [`Unusedglobproof.v`](Nominal-CompCert-Struct-Memspace/backend/Unusedglobproof.v),
  the invariant `match_states_regular` now carries two new
  assumptions:

  ```
  (SMJ: j = struct_meminj (Mem.support m))
  (MSTK: Mem.stack(Mem.support m) = Mem.stack(Mem.support tm))
  ```

  Here, `SMJ` asserts that the injection is a structural one, while
  `MSTK` asserts that the stack tree is exactly the same before and
  after the transformation (lines 925-926) as `Unusedglob` does not
  touch stack at all. With this very precise invariant, we know that
  at any point of regular execution, the stack frames are not changed
  at all. As a result, the proof becomes much more intuitive.

  Similar observations can be made for other passes. For example, in
  [`SimplLocalsproof.v`](Nominal-CompCert-Struct-Memspace/cfrontend/SimplLocalsproof.v),
  we have the following new invariants:
 
  ```
  (VINJ: j = struct_meminj (Mem.support m))
  (MSTK: Mem.stackseq m tm)
  ```

  where `Mem.stackseq` holds if the stack trees have the same
  structure. This help us convert reasoning about the whole stack
  memory into that for individual stack frames.

  Note that we do not claim our proof is simpler than before because the
  new proof is still built on top of the old one. To get a simpler proof,
  we will need to rewrite the whole proof from scratch. This is left for
  future work. The same observation can be made for the other compiler passes
  mentioned in Sec 2.4.1, including SimplLocals, Cminorgen and Stacking.

### Verified compilation of programs with contextual memory

(Section 5.1) The above definitions of structural memory injection
already assumes that stack blocks allocated by external function calls
are mapped to themselves. Therefore, the assumption of compilation
under contextual programs is already manifested in this extension.


## Extension 3: Stack-Aware Nominal CompCert

This extension is implemented in the directory
[`Stack-Aware-Nominal-CompCert`](Stack-Aware-Nominal-CompCert) and
correspond to the contents in Section 5.2.

- (Definition 5.1) The abstract stack is defined in
  [`common/Memory.v`](Stack-Aware-Nominal-CompCert/common/Memory.v). In
  particular, the section `STACKADT` contains the following
  formalization of Definition 5.1:

  ```
  Record frame : Type :=
  {
    frame_size : Z;
    frame_size_pos: (0 <= frame_size)%Z;
  }.
  
  Definition stage := list frame.
  Definition stackadt := list stage.
  ```
  
- (Line 1018) The function `stack_size` calculates the size of an abstract
  stack by adding all the sizes of its frames together, as follows:
  
  ```
  Fixpoint stack_size (s:stackadt): Z :=
    match s with
    |nil => 0
    |hd::tl => size_of_all_frames hd + stack_size tl
    end.
  ```
  
  Note that this is an over-approximation of the size consumption
  when a stage contains multiple frames allocated by a sequences of
  tail calls because only the top-most tail call is alive.

  Some important properties about this function are also proved.

- (Line 1019) The maximal stack size is defined as the following constant:

  ```
  Definition max_stacksize : Z := 4096.
  ```

- (Lines 1020-1022) The new support has the following type
  
  ```
  Record sup' : Type := mksup {
    stack : stree;
    astack : stackadt;
    global : list ident;
  }.
  ```

- (Lines 1023-1040) The functions for manipulating the abstract stack,
  including `push_stage`, `record_frame` (i.e., `record` in the paper)
  and `pop_stage` are defined in
  [`common/Memory.v`](Stack-Aware-Nominal-CompCert/common/Memory.v),
  together with a collection of properties about them.

- (Lines 1041-1050) To prove semantics preservation, we updated the
  semantics of each language with operations over abstract stack using
  the `stackspace` oracle. We take
  [`cfrontend/Clight.v`](Stack-Aware-Nominal-CompCert/cfrontend/Clight.v)
  as an example:

  + The following parameter denotes the oracle `stackspace` in the paper:

    ```
    Variable fn_stack_requirements : ident -> Z.
    ```

  + On function entry, a new stage is created and a frame is
    recorded whose size is determined by the oracle. For example, we
    have
    
    ```
    Inductive function_entry1 (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) (id:ident) : Prop :=
    | function_entry1_intro: forall m0 m1 m2 path,
      ...
      (* push_stage and record_frame *)
      Mem.record_frame (Mem.push_stage m1) (Memory.mk_frame (fn_stack_requirements id )) = Some m2 ->
      ...
    ```

  + On function return, the top-most stage is popped. For example, we have

    ```
    Inductive step: state -> trace -> state -> Prop :=
    ...
    | step_return_0: forall f k e le m m' m'' m''',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      Mem.return_frame m' = Some m'' ->
      (* pop_stage *)
      Mem.pop_stage m'' = Some m''' ->
      step (State f (Sreturn None) k e le m)
           E0 (Returnstate Vundef (call_cont k) m''')
    ...
    ```

  + The semantics preservation theorems now use the updated semantics
    and depend on the oracle. For example, the simulation theorem in
    [`cfrontend/SimplLocalsproof.v`](Stack-Aware-Nominal-CompCert/cfrontend/SimplLocalsproof.v)
    is stated as follows:

    ```
    Theorem transf_program_correct:
      forward_simulation (semantics1 fn_stack_requirements prog)
                         (semantics2 fn_stack_requirements tprog).
    ```

- (Lines 1051-1060) The new semantics preservation proofs rely on two
  semantics for RTL that calculates stack consumption in two different
  ways:
  
  + In [`backend/RTL.v`](Stack-Aware-Nominal-CompCert/backend/RTL.v),
    a regular call pushes a new stage while a tailcall does not. When
    an internal function is entered, a new frame is recorded on the
    top-most stage. Since `stack_size` calculates the stack size by
    adding up the sizes of frames, the stack size consumption
    incurred by regular calls and tail calls to the same function is
    the same. This matches with the description in Fig. 8 and is
    formalized in the following definition of the small-step
    transition:
  
    ```
    Inductive step: state -> trace -> state -> Prop :=
    ...
    | exec_Icall:
        forall s f sp pc rs m sig ros args res pc' fd id,
        ...
        (* push_stage *)
        step (State s f sp pc rs m)
             E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args (Mem.push_stage m) id)
    | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m' m'' id,
        ...
        (* No push_stage *)
        step (State s f (Vptr stk Ptrofs.zero) pc rs m)
             E0 (Callstate s fd rs##args m'' id)
    | exec_function_internal:
      forall s f args m m' m'' stk id path m''',
        ...
        (* record_frame *)
        Mem.record_frame m'' (Memory.mk_frame (fn_stack_requirements id)) = Some m''' ->
        step (Callstate s (Internal f) args m id)
             E0 (State s f (Vptr stk Ptrofs.zero) f.(fn_entrypoint)
                 (init_regs args f.(fn_params)) m''')
    | exec_return:
      forall res f sp pc rs s vres m m',
        (* pop_stage *)
        Mem.pop_stage m = Some m' ->
        step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
             E0 (State s f sp pc (rs#res <- vres) m').
    ...
    ```

  + In
    [`backend/RTLmach.v`](Stack-Aware-Nominal-CompCert/backend/RTLmach.v),
    the `push_stage` and `record_frame` are merged and only happen
    when entering an internal function. Moreover, the top-most stage
    is popped upon a tailcall. As a result, the abstract stack now
    matches with the call stack, such that each of its stage contains
    only one frame corresponding to an activation record. Moreover, the
    result of applying `stack_size` on this abstract stack is the
    actual stack consumption at the machine level (hence the name
    `RTLmach`). This is formalized in the definition of the small-step
    transition, as follows:

    ```
    Inductive step: state -> trace -> state -> Prop :=
    ...
    | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd id,
      ...
      (* No operation on the abstract stack *)
      step (State s f sp pc rs m)
           E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m id)
    | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m' id m'' m''',
      ...
      (* pop_stage *)
      Mem.pop_stage m'' = Some m''' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
           E0 (Callstate s fd rs##args m''' id)
    | exec_function_internal:
      forall s f args m m' m'' m''' stk id path,
      ...
      (* push_stage and record_frame *)
      Mem.record_frame (Mem.push_stage m'')(Memory.mk_frame (fn_stack_requirements id)) = Some m''' ->
      step (Callstate s (Internal f) args m id)
           E0 (State s f (Vptr stk Ptrofs.zero) f.(fn_entrypoint)
               (init_regs args f.(fn_params)) m''')
    | exec_Ireturn:
      forall s f stk pc rs m or m' m'' m''',
      ...
      (* pop_stage *)
      Mem.pop_stage m'' = Some m''' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
           E0 (Returnstate s (regmap_optget or Vundef rs) m''')
    ...
    ```      

  + We define an identity transformation at the RTL level in
    [`backend/RTLmachproof.v`](Stack-Aware-Nominal-CompCert/backend/RTLmachproof.v):

    ```
    Definition transf_program (p: program) : program := p.
    ```

    We then prove the forward simulation between the above two
    semantics over the same RTL program in
    [`backend/RTLmachproof.v`](Stack-Aware-Nominal-CompCert/backend/RTLmachproof.v):

    ```
    Theorem transf_program_correct:
      forward_simulation (RTL.semantics fn_stack_requirements prog)
                         (RTLmach.semantics fn_stack_requirements tprog).
    ```

    We insert the identity transformation into the compilation chain
    after `Inlining` in
    [`driver/Compiler.v`](Stack-Aware-Nominal-CompCert/driver/Compiler.v)
    and use the above simulation theorem to prove its correctness.

    ```
    Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
    OK f
    @@ print (print_RTL 0)
    @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
    @@ print (print_RTL 1)
    @@@ time "Inlining" Inlining.transf_program
    @@ time "RTLmach" RTLmachproof.transf_program
    ...
    ```

- The verified compilation chain of vanilla CompCert ends at assmebly languages.
  In this extension, the assembly language
  [`Asm`](Stack-Aware-Nominal-CompCert/x86/Asm.v) is complied into
  [`RealAsm`](Stack-Aware-Nominal-CompCert/x86/RealAsm.v) by following
  the same passes in Stack-Aware CompCert (see [1]). We have
  implemented and proved these passes for the x86 backend.

  + An alternative x86 assembly semantics (called `Single-Stack Asm`)
    that makes use of a single and contiguous stack is defined in
    [`x86/SSAsm.v`](Stack-Aware-Nominal-CompCert/x86/SSAsm.v). Note
    that `Single-Stack Asm` still uses pseudo registers and
    instructions like `Asm`. A forward simulation between `Asm`
    semantics and `Single-Stack Asm` is proved in
    [`x86/SSAsmproof.v`](Stack-Aware-Nominal-CompCert/x86/SSAsmproof.v). This
    proof makes critical use of abstract stack to merge the individual
    stack frames into a single and contiguous stack.

  + A third x86 Asm semantics (i.e., `RealAsm`) is defined
    [`x86/RealAsm.v`](Stack-Aware-Nominal-CompCert/x86/RealAsm.v). `RealAsm`
    no longer relies on pseudo registers or instructions. A backward
    simulation between `Single-Stack Asm` and `RealAsm` is proved in
    [`x86/RealAsmproof.v`](Stack-Aware-Nominal-CompCert/x86/RealAsmproof.v). This
    proof is almost identical to the one in Stack-Aware CompCert.

- (Theorem 5.2) The final correctness theorem is defined in
  [`driver/Compiler.v`](Stack-Aware-Nominal-CompCert/driver/Compiler.v),
  as follows:

  ```
  Theorem transf_c_program_correct_real: forall p tp,
    transf_c_program_real p = OK tp ->
    backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (RealAsm.semantics tp).
  ```

  Note that the instance of the oracle `stackspace` is extracted from the target
  program `tp` by calling a concrete definition for
  `fn_stack_requirements`, as follows:

  ```
  Definition fn_stack_requirements (tp: Asm.program) (id: ident) : Z :=
     match Globalenvs.Genv.find_funct_ptr (Globalenvs.Genv.globalenv tp) (Values.Global id) with
     | Some (Internal f) => Asm.fn_stacksize f
     | _ => 0
     end.
  ```


## Extension 4: Multi-Stack CompCert

This extension is implemented in the directory
[`Multi-Stack-CompCert`](Multi-Stack-CompCert) and correspond to the
contents in Section 5.3 and 5.4.

- (Lines 1092-1095) The definition of supports (in
  [`common/Memory.v`](Multi-Stack-CompCert/common/Memory.v)) is
  generalized to contain multiple stack trees and abstract stacks:

  ```
  Record sup' : Type := mksup {
    stacks : list stree;
    astacks : list stackadt;
    global : list ident;
  
    sid : nat;
    sid_valid : (length stacks > sid)%nat;
    length_eq : length stacks = length astacks
  }.
  ```
  
  Here, `sid` denotes the index to the stack being focused on in the
  fields `stacks` and `astacks`. 

- (Lines 1096-1098) The following functions are used to access the focused stack:

  ```
  Definition stack (s:sup) := nth (sid s) (stacks s) empty_stree.
  Definition astack (s:sup) := nth (sid s)(astacks s) nil.
  ```

- (Lines 1099-1107) The proofs of Stack-Aware Nominal CompCert are
  updated straightforwardly by using the above definitions. The final
  theorem of Multi-Stack CompCert is located in
  [`driver/Compiler.v`](Multi-Stack-CompCert/driver/Compiler.v):

  ```
  Theorem transf_c_program_correct_real:
  forall p tp,
    transf_c_program_real p = OK tp ->
    backward_simulation (Csem.semantics (fn_stack_requirements tp) p) (RealAsm.semantics tp).
  ```

  It looks similar to that of Stack-Aware Nominal CompCert, except
  that the semantics are updated with the usage of multiple stacks.

- (Section 5.4.2) The thread-safe compilation is exactly the same as
  in Multi-Stack CompCert. The thread-safe linking is part of the CCAL
  framework which we do not include in this artifact. This is because
  the newest implementation of CCAL is based on an older version of
  Coq (v8.4) which is not compatible with Coq v8.12 or CompCert
  v3.8. However, since the key concept of thread-safe linking (i.e.,
  linking of multiple stacks, see [2]) is fully supported by our
  memory model with multiple and contiguous stacks, its realization
  is straightforward once the CCAL framework is updated to Coq v8.12.

## Evaluation

The following are the instructions for reproducing the lines of code (LOC) in
Table 1 and 2. All the commands in the following instructions should be executed
under the directory 'nominal-compcert-popl22-artifact'.

### Table 1

#### Column 2

The results in the second column can be produced by running:
```
    coqwc CompCert-3.8/common/Memory.v CompCert-3.8/common/Memtype.v CompCert-3.8/common/Globalenvs.v CompCert-3.8/cfrontend/SimplLocalsproof.v CompCert-3.8/cfrontend/Cminorgenproof.v CompCert-3.8/backend/Inliningproof.v  CompCert-3.8/backend/ValueAnalysis.v CompCert-3.8/backend/Unusedglobproof.v
```
This command lists the lines of code (LOC) for files in CompCert 3.8 that also
appear in the Table 1 in three categories: 'spec', 'proof' and 'comments'. The
numbers in column 2 are obtained by adding the numbers in 'spec' and 'proof' for each file.

The number at the row 'Total' is the summation of LOC for all coq files(.v).
It is obtained by running:
```
    coqwc CompCert-3.8/*/*.v
```
and adding the numbers in the 'spec' and 'proof' categories in the last line.

#### Column 3
The numbers in column 3 can be obtained in a similar way. Run the following command:
```
    coqwc Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Memtype.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Unusedglobproof.v
```
and add the numbers in 'spec' and 'proof' to get the results in column 3.
For the result at the row 'Total', run
```
    coqwc Nominal-CompCert/*/*.v
```
and add the numbers in 'spec' and 'proof' in the last line.

#### Column 6
The results in column 6 were manually collected from the
[github compare page](https://github.com/SJTU-PLV/CompCert/compare/478ece4...7fe44a1).
For each file, the number is the bigger one among "additions" and "deletions",
with the number of empty lines subtracted.

### Table 2

#### Column 2
Similar to the Table 1, the results in column 2 can be produced by running
```
    coqwc Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Unusedglobproof.v Nominal-CompCert/backend/Stackingproof.v
```
and add the numbers in 'spec' and 'proof' for each file.

For the result at the row 'Total', run
```
    coqwc Nominal-CompCert/*/*.v
```
and add the numbers in 'spec' and 'proof' in the last line.

#### Column 3
For seperate files, run
```
    coqwc Nominal-CompCert-Struct-Memspace/common/Memory.v Nominal-CompCert-Struct-Memspace/common/Globalenvs.v Nominal-CompCert-Struct-Memspace/cfrontend/SimplLocalsproof.v Nominal-CompCert-Struct-Memspace/cfrontend/Cminorgenproof.v  Nominal-CompCert-Struct-Memspace/backend/Unusedglobproof.v Nominal-CompCert-Struct-Memspace/backend/Stackingproof.v
```
For 'Total' result, run
```
    coqwc Nominal-CompCert-Struct-Memspace/*/*.v
```
#### Column 6
For seperate files, run
```
    coqwc Stack-Aware-Nominal-CompCert/common/Memory.v Stack-Aware-Nominal-CompCert/common/Globalenvs.v Stack-Aware-Nominal-CompCert/cfrontend/SimplLocalsproof.v Stack-Aware-Nominal-CompCert/cfrontend/Cminorgenproof.v  Stack-Aware-Nominal-CompCert/backend/Unusedglobproof.v Stack-Aware-Nominal-CompCert/backend/Stackingproof.v
```
For 'Total' result, run
```
    coqwc Stack-Aware-Nominal-CompCert/*/*.v
```
#### Column 9
For seperate files, run
```
    coqwc Multi-Stack-CompCert/common/Memory.v Multi-Stack-CompCert/common/Globalenvs.v Multi-Stack-CompCert/cfrontend/SimplLocalsproof.v Multi-Stack-CompCert/cfrontend/Cminorgenproof.v  Multi-Stack-CompCert/backend/Unusedglobproof.v Multi-Stack-CompCert/backend/Stackingproof.v
```
For 'Total' result, run
```
    coqwc Multi-Stack-CompCert/*/*.v
```
## References

[1] *An Abstract Stack Based Approach to Verified Compositional
    Compilation to Machine Code*. Yuting Wang, Pierre Wilke, and Zhong
    Shao. The 46th ACM SIGPLAN Symposium on Principles of Programming
    Languages (POPL), 2019.

[2] *Certified Concurrent Abstraction Layers*. Ronghui Gu, Zhong Shao,
    Jieung Kim, Xiongnan (Newman) Wu, Jérémie Koenig, Vilhelm Sjöberg,
    Hao Chen, David Costanzo, and Tahina Ramananandro. The 2018 ACM
    SIGPLAN Conference on Programming Language Design and
    Implementation (PLDI), 2018.
