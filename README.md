# Verified Compilation of C Programs with a Nominal Memory Model (Artifact for POPL 2022)

## Overview

This artifact consists of a series of extensions to CompCert (v3.8)
based on a nominal memory model, as follows:

1. Nominal CompCert
2. Nominal CompCert with Structured Memory Space
3. Stack-Aware Nominal CompCert
4. Multi-Stack CompCert

The complete source code of each exentsion can be found in a
corresponding top-level directory (we have included a copy of CompCert
v3.8 for comparison and reference). The artifact accompanies the
following paper:

  > *Verified Compilation of C Programs with a Nominal Memory Model*.
    Yuting Wang, Ling Zhang, Zhong Shao and Jeremie Koenig

As described in the paper, these extensions are developed
incrementally, with Nominal CompCert as the basic extension of
CompCert based on the nominal memory model, and Multi-Stack CompCert as
the most sophisticated extension that combines all the features
introduced in the paper. Moreoever, they correspond to the main claims
we make in Section 1.3 of the paper, as follows:

1. The nominal memory model is a natural extension of the block-based
memory model. It enables flexible formalization of block ids and
eliminates global assumptions on memory space. These claims are
justifed by the general realization of nominal memory model in Nominal
CompCert.

2. Nominal CompCert is an extension with the full compilation chain of
CompCert verified and a general framework for verified compilation of
C programs. This is justified by the implemenation of Nominal CompCert.

3. We developed an extension of Nominal CompCert that enables
intuitive reasoning of compiler transformations on partial
memroy. This is justified by Nominal CompCert with Structured Memory
Space.

4. We developed extensions of Nominal CompCert that enable modular
reasoning about open programs with contexual memory. This is justified
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
presentation. Simply run the followning command (which needs
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

### Nominal Memory Model

The nominal memory model is introduced Section 3.2. Its constituents
are listed as follows:

- The interface for nominal block ids `BLOCK` is defined in `common/Values.v`.

- The instantiation of `BLOCK` with postive ids is defined by the Coq
  module `Block` in `common/Values.v`.

- The interface for supports `SUP` is defined in `common/Memtype.v`.

- The instantiation of supports as a list of block ids is defined by the module `Sup` in `common/Memory.v'.

- The updated memory state `mem` is defined in `common/Memory.v` with
  a new field `support:sup`.  The updated definition of `valid_block`
  can also be found in this file. The basic properties of the memory
  model have been reproved with these changes.

### Nominal CompCert

Nominal CompCert is introduced in Section 3.3. The corresponding
changes w.r.t. CompCert are listed as follows:

- One main difference is that operations over next
  blocks are changed to those over supports. For instance, in
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
  We elide a dicussion of similar changes.

- Finally, Theorem 3.1 is defined in `driver/Compiler.v` as the
  following Coq theorem:
  ```
  Theorem transf_c_program_correct:
    forall p tp,
    transf_c_program p = OK tp ->
    backward_simulation (Csem.semantics p) (Asm.semantics tp).
  ```

