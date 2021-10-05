# Verified Compilation of C Programs with a Nominal Memory Model (Artifact for POPL 2022)

## Overview

This artifact consists of a series of extensions to CompCert (v3.8)
based on a nominal memory model, as follows:

1. Nominal CompCert
2. Nominal CompCert with Structured Memory Space
3. Stack-Aware Nominal CompCert
4. Multi-Stack CompCert

The complete source code of each exentsion can be found in a
corresponding top-level directory. The artifact accompanies the
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

## Nominal CompCert

In the remaining sections, we present the details of each extension
and show their correspondence to the discussion in the paper. We first
discuss Nominal CompCert.


