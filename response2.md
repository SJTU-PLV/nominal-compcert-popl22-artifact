Thanks for pointing out the discrepancy. There are two things we want to clarify:

1. Stack-Aware Nominal CompCert actually contains more compilation
   passes than Stack-Aware CompCert. The original Stack-Aware CompCert
   stops at Asm (See [Wang et al., POPL2019]). However, Stack-Aware
   Nominal CompCert further compiles Asm programs into RealAsm
   programs. These compiler passes are implemented and verified in the
   following files in the `x86` directory:

   ```
   AsmFacts.v AsmRegs.v SSAsm.v SSAsmproof.v RealAsm.v RealAsmgen.v RealAsmproof.v
   ```
   
   Therefore, the remark we made about the comparison between
   Stack-Aware Nominal CompCert and Stack-Aware CompCert at line 1125-1126 was really
   intended to compare the compiler passes down to Asm level (not
   including the above passes that do not exist in Stack-Aware
   CompCert). 

   We realized that it was quite confusing to talk about a comparison
   between parts of Stack-Aware Nominal CompCert with the full
   Stack-Aware CompCert. We will fix the discussion about this
   comparison in the final version of the paper.

2. You can count the LOC of Stack-Aware Nominal CompCert excluding the
   files for compiling Asm to RealAsm, by running the following
   command in the `Stack-Aware-Nominal-CompCert` directory (note that
   for consistency with the previous results the flocq library is
   excluded):

   ```
   find . -name "*.v" | sed "/flocq\|SSAsm\|RealAsm\|AsmFacts\|AsmRegs/d" | xargs coqwc
   ```

   It gives the following results:

   ```
   authors@authors:~/nominal-compcert-popl22-artifact/Stack-Aware-Nominal-CompCert$ find . -name "*.v" | sed "/flocq\|SSAsm\|RealAsm\|AsmFacts\|AsmRegs/d" | xargs coqwc
       spec     proof    comments
       ......
       74045    71313    15011 total
   ```

   So the increase in LOC w.r.t. Nominal CompCert is 74045 + 71313 -
   137342 = 8016.  This result is 3k lines more than what we claimed
   at line 1125 and is reflected in the result shown by the
   reviewer. This is due to the fact that, after we submitted the
   paper, we have adjusted where the operations of pushing and poping
   stages and of recording and returning frames should occur in the
   semantics of CompCert's languages (See the discussion of these
   semantics shown in README.md), to better align the internal
   operations on stages and frames with the external operations on
   them (by external calls). We believe this will facilitate the
   future development of compositional compilation. However, this also
   has a cascading effect such that we need to prove more properties
   for memory operations and have a bit more complicated proofs for
   some of the compiler passes. That is why there is 3k more
   LOC. Still, comparing to the 21k LOC of Stack-Aware CompCert, the
   8k in our artifact is much more lightweight. We will update the
   statistics and Table 2 to reflect these changes in our final
   submission.

