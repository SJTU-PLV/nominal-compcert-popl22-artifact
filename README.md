# Verified Compilation of C Programs with a Nominal Memory Model (Artifact for POPL 2022)

## Overview

This artifact consists of a series of extensions to CompCert (v3.8)
based on a nominal memory model, as follows:

1. Nominal CompCert
2. Nominal CompCert with Structured Memory Space
3. Stack-Aware Nominal CompCert
4. Multi-Stack CompCert

The complete source code of each extension can be found in a
corresponding top-level directory (we have included a copy of CompCert
v3.8 for comparison and reference). The artifact accompanies the
following paper:

  > *Verified Compilation of C Programs with a Nominal Memory Model*.
    Yuting Wang, Ling Zhang, Zhong Shao and Jeremie Koenig

As described in the paper, these extensions are developed
incrementally, with Nominal CompCert as the basic extension of
CompCert based on the nominal memory model, and Multi-Stack CompCert as
the most sophisticated extension that combines all the features
introduced in the paper. Moreover, they correspond to the main claims
we make in Section 1.3 of the paper, as follows:

1. The nominal memory model is a natural extension of the block-based
memory model. It enables flexible formalization of block ids and
eliminates global assumptions on memory space. These claims are
justified by the general realization of nominal memory model in Nominal
CompCert.

2. Nominal CompCert is an extension with the full compilation chain of
CompCert verified and a general framework for verified compilation of
C programs. This is justified by the implementation of Nominal CompCert.

3. We developed an extension of Nominal CompCert that enables
intuitive reasoning of compiler transformations on partial
memory. This is justified by Nominal CompCert with Structured Memory
Space.

4. We developed extensions of Nominal CompCert that enable modular
reasoning about open programs with contextual memory. This is justified
by Stack-Aware Nominal CompCert and Multi-Stack CompCert.

5. The above developments are lightweight and easy to adopt. This can
be observed by comparing our extensions with CompCert v3.8.

We shall delve into the details of these extensions later.


## Compilation and Testing

### Prerequisites

This artifact is based on CompCert v3.8 and needs Coq v8.12 to
compile. All the required software have already been installed on the
virtual machine. If you prefer to compiled the source code on your own
computer, then we suggest you install the prerequisites via
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

The compilation should start and terminate successfully.  

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

To check that our CompCert extensions work for compilation, you can
run the test cases in the `test` directory, as follows:

```
  make
  make test
```


## Extension 1: Nominal CompCert

In the remaining sections, we present the details of each extension
and show their correspondence to the discussion in the paper. We first
discuss the nominal memory model and Nominal CompCert, which are
implemented in the directory `Nominal-CompCert` and correspond to the
contents in Section 3 of the paper.

### Nominal memory model

The nominal memory model is introduced Section 3.2. Its constituents
are listed as follows:

- The interface for nominal block ids `BLOCK` is defined in `common/Values.v`.

- The instantiation of `BLOCK` with positive ids is defined by the Coq
  module `Block` in `common/Values.v`.

- The interface for supports `SUP` is defined in `common/Memtype.v`.

- The instantiation of supports as a list of block ids is defined by the module `Sup` in `common/Memory.v'.

- The updated memory state `mem` is defined in `common/Memory.v` with
  a new field `support:sup`.  The updated definition of `valid_block`
  can also be found in this file. The basic properties of the memory
  model have been reproved with these changes.

### Nominal CompCert

Nominal CompCert is introduced in Section 3.3. As described in the
paper, Nominal CompCert updates the full compilation chain of CompCert
with the nominal memory model. Besides the generalized memory model we
have discussed above, the changes w.r.t. CompCert are mainly about the
semantics of languages and updates of proofs. These changes are not
very big and listed as follows:

- One main difference is that next blocks are replaced by supports
  along with the related properties. For instance, in
  `cfrontend/Cminorgenproof.v` in CompCert v3.8, there was an old
  lemma stating that next block is not changed by the operation
  `free_list`:

  ```
  Lemma nextblock_freelist:
    forall fbl m m',
    Mem.free_list m fbl = Some m' ->
    Mem.nextblock m' = Mem.nextblock m.
  ```

  It is generalized to the following theorem about support:

  ```
  Lemma support_freelist:
    forall fbl m m',
      Mem.free_list m fbl = Some m' ->
      Mem.support m' = Mem.support m.
  ```

  There exists many other small changes with the same nature; we
  elide a discussion of them.

- The changes to valid blocks discussed at lines 526-532 is
  demonstrated in `backend/Inliningproof.v`. Previously, the
  invariant `match_stacks_cons` assumes:

  ```
    (BELOW: Plt sp' bound)
  ```

  which guarantees that `sp'` is a valid block.  In Nominal CompCert,
  the next block `bound` is changed to `support` and the above
  proposition is broken into two:

  ```
    (SPS': sp' = fresh_block sps')
    ...
    (BELOW: Mem.sup_include (sup_add sp' sps') support)
  ```

  We elide a discussion of similar changes.

- The proofs are updated accordingly with the above changes. The final
  theorem (Theorem 3.1) is proved in `driver/Compiler.v` as follows:

  ```
  Theorem transf_c_program_correct:
    forall p tp,
    transf_c_program p = OK tp ->
    backward_simulation (Csem.semantics p) (Asm.semantics tp).
  ```

## Extension 2: Nominal CompCert with Structured Memory Space

   This extension is implemented in the directory
   `Nominal-CompCert-Struct-Memspace` and correspond to the contents
   in Section 4 and 5.1.

### Nominal memory model with structured space

  This instantiation of nominal memory model is introduced in Section
  4.1. Its constituents are described as follows:

  - (Section 4.1.1) `fid`, `path` and the module `Block` are defined in
    `common/Values.v`.

  - (Section 4.1.2) `stree` is defined in `common/Memory.v`, together
    with its operations `next_stree`, `next_block_stree`,
    `return_stree` and `stree_in` and their properties. A well-founded
    induction principle `stree_ind` is also established for induction
    over strees.

  - (Section 4.1.3) The formalization of support, i.e., module `Sup`,
    is defined in `common/Memory.v`. 

  - (Section 4.1.4) The memory operations `alloc_glob`, `alloc_frame`,
    `return_frame` and `alloc_block` are defined in `common/Memory.v`.
    Essential properties about these operations are also proved there.

### Nominal CompCert with structured memory space

  This extension is introduced in Section 4.2. The updates to semantics
  of CompCert's languages are as follows:

  - (Lines 713-715) Originally, the allocation global variables in the
   function `alloc_global` in `common/Globalenvs.v` is done by using
   the `alloc` method. In this extension, `alloc_global` is used instead.

  - (Line 716) `alloc_frame` and `return_frame` are added to function
    calls and returns. For example, in Cminor, the small-step
    transition is changed from

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

   to 

   ```
    Inductive step: state -> trace -> state -> Prop :=
    ...
    | step_return_0: forall f k sp e m m' m'',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      Mem.return_frame m' = Some m'' ->
      step (State f (Sreturn None) k (Vptr sp Ptrofs.zero) e m)
        E0 (Returnstate Vundef (call_cont k) m'')
    ...
    | step_internal_function: forall f vargs k m m' m'' sp e path id,
      Mem.alloc_frame m id = (m', path) ->
      Mem.alloc m' 0 f.(fn_stackspace) = (m'', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k m id)
        E0 (State f f.(fn_body) k (Vptr sp Ptrofs.zero) e m'')
    ...
   ```

  - (Line 717) In our artifact, `alloc` is updated to have the same
    implementation as `alloc_block`. Therefore, we have reused the
    `alloc` method for allocation of stack blocks.

  - With the above changes, we are able to update the complete proofs
    of CompCert, the final correctness theorem is again found at
    `transf_c_program_correct` in `driver/Compiler.v`.

### Intuitive proofs for partial memory transformation

 This corresponds to the discussion in Section 4.3. We have updated
 the proofs for `SimplLocals`, `Cminorgen`, `Unusedglob` and
 `Stacking` to use structural memory injections. They are formalized
 in `cfrontend/SimplLocalsproof.v`, `cfronend/Cminorgenproof.v`,
 `backend/Unusedglobproof.v` and `backend/Stackingproof.v`.

 - (Section 4.3.1) For each pass, its structural memory injection is
   defined as the function `struct_meminj`. The implementation of
   `struct_meminj` varies with different passes. For example,
   `struct_meminj` for `Unusedglobal` (lines 764-769) is defined in
   `backend/Unusedglobproof.v` as follows:
   
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

  and `struct_meminj` for `Cminorgen` (lines 804-809) is defined in
  `cfrontend/Cminorgenproof.v` as follows:

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

 - (Section 4.3.2 and 4.3.3.) With the structured memory injection, we
   are able to simplify the reasoning about stack memory. For example,
   in `Unusedglobalproof.v`, the invariant `match_states_regular` now
   carries two new assumptions:

   ```
     (SMJ: j = struct_meminj (Mem.support m))
     (MSTK: Mem.stack(Mem.support m) = Mem.stack(Mem.support tm))
   ```

   Here, `SMJ` asserts that the injection is a structural one, while
   `MSTK` asserts that the stack tree is exactly the same before and
   after the transformation (as `Unusedglob` does not touch stack at
   all). With this very precise invariant (thanks to the structural
   injection), we know that at any point of regular execution, the
   stack frames are not changed at all. As a result, the proof becomes
   much more intuitive. 

   Similar observations can be made for other passes. For example, in
   `SimplLocalsproof.v`, we have the following new invariants:
   
   ```
    (VINJ: j = struct_meminj (Mem.support m))
    (MSTK: Mem.stackseq m tm)
   ```

   where `Mem.stackseq` holds if the stack trees have the same
   structure. This help us convert reasoning about the whole stack
   memory into that for individual stack frames.


### Verified compilation of programs with contextual memory

  The above definitions of structural memory injection already assumes
  that stack blocks allocated by external function calls are mapped to
  themselves. Therefore, the assumption of compilation under
  contextual programs is already manifested in this extension, as discussed
  in Section 5.1.


## Extension 3: Stack-Aware Nominal CompCert

## Extension 4: Multi-Stack CompCert