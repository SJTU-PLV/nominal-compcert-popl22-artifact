Firstly, since we have been working on this artifact after the paper submission, the results reproduced on codes here are slightly different from the results from the tables in the paper.

### Table 1
The results in first two columns generally can be produced by(in path nominal-compcert-popl22-artifact):
```
coqwc [version]/*/*.v
```
Which will print LOCs for all the .v files and the total lines(appear in Table1 and Table2) for each version. For the specific files we listed in Table1, copy and run:
```
coqwc CompCert-3.8/common/Values.v CompCert-3.8/common/Memory.v CompCert-3.8/common/Memtype.v CompCert-3.8/common/Globalenvs.v CompCert-3.8/cfrontend/SimplLocalsproof.v CompCert-3.8/cfrontend/Cminorgenproof.v CompCert-3.8/backend/Inliningproof.v  CompCert-3.8/backend/ValueAnalysis.v CompCert-3.8/backend/Unusedglobproof.v;coqwc Nominal-CompCert/common/Values.v Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Memtype.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Unusedglobproof.v

```
The results in the third column was manually collected from the [github compare page](https://github.com/SJTU-PLV/CompCert/compare/478ece4...e9c10d5). The number is around the larger one of additions and deletions, the difference comes from empty lines. The third column is simply the ratio of the first and the third colomn.

### Table 2
Similar to Table1, copy and run:
```
coqwc Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/common/Events.v Nominal-CompCert/common/Separation.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Tailcallproof.v  Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Stackingproof.v; coqwc Stack-Aware-Nominal-CompCert/common/Memory.v Stack-Aware-Nominal-CompCert/common/Globalenvs.v Stack-Aware-Nominal-CompCert/common/Events.v Stack-Aware-Nominal-CompCert/common/Separation.v Stack-Aware-Nominal-CompCert/backend/RTLmach.v Stack-Aware-Nominal-CompCert/backend/RTLmachproof.v Stack-Aware-Nominal-CompCert/cfrontend/SimplLocalsproof.v Stack-Aware-Nominal-CompCert/cfrontend/Cminorgenproof.v Stack-Aware-Nominal-CompCert/backend/Tailcallproof.v  Stack-Aware-Nominal-CompCert/backend/Inliningproof.v  Stack-Aware-Nominal-CompCert/backend/ValueAnalysis.v Stack-Aware-Nominal-CompCert/backend/Stackingproof.v
```

For the "Total" line of both tables, you can run the mentioned $coqwc$ commmand on each version and check the results. We also provide a [shell footnote](https://github.com/SJTU-PLV/nominal-compcert-popl22-artifact/blob/main/total.sh) on github to print only the total lines appeared in Table1 and Table2.
### sudo password
There is no need to enter a password to run sudo in the virtual machine.
