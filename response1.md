Firstly, since we have been working on this artifact after the paper submission, the results reproduced on codes here are slightly different from those in the paper.

All the mentioned commands here should be executed in path 'nominal-compcert-popl22-artifact'.
### Table1
The results in the first column can be produced by:
```
coqwc CompCert-3.8/common/Values.v CompCert-3.8/common/Memory.v CompCert-3.8/common/Memtype.v CompCert-3.8/common/Globalenvs.v CompCert-3.8/cfrontend/SimplLocalsproof.v CompCert-3.8/cfrontend/Cminorgenproof.v CompCert-3.8/backend/Inliningproof.v  CompCert-3.8/backend/ValueAnalysis.v CompCert-3.8/backend/Unusedglobproof.v
```
This command will list the 'spec', 'proof' and 'comments' lines of code(LOC) of the files appear in the Table1 seperately. Adding the 'spec' and 'proof' columns will give the results in column1.
In addition, row 'Total' in Table1 is the summary of the LOCs of all coq files(.v) instead of the listed ones, which can be printed by running:
```
coqwc CompCert-3.8/*/*.v
```
The command will print the LOCs for all the .v files in the 'Compcert-3.8' path and the total number **in the last row of output**. Similarly adding the 'spec' and 'proof'(i.e. the first two numbers in the last line) will give the result in row 'Total', column1.

For column2, similarly copy and run:
```
coqwc Nominal-CompCert/common/Values.v Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Memtype.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Unusedglobproof.v
```
Adding the numbers in column 'spec' and 'proof' will give the results in the column2. For the result in row 'Total', run
```
coqwc Nominal-CompCert/*/*.v
```
and add the first two numbers **in the last row of output**.

The results in the third column was manually collected from the [github compare page](https://github.com/SJTU-PLV/CompCert/compare/478ece4...e9c10d5). The numbers are around the larger ones of additions and deletions(lines of code) of the files, the differences come from empty lines. The last column is simply the ratio of the column3 and column1.

### Table 2
In Table2, we list the lines of 'spec' and 'proof' code separately instead of the sum of them. For the first and the third columns(`Nominal-CompCert` version), copy and run:
```
coqwc Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/common/Events.v Nominal-CompCert/common/Separation.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Tailcallproof.v  Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Stackingproof.v
```
The first two columns of the output ('spec' and 'proof') respectively correspond to column1 and column3 in Table2. The `RTLmach.v` and `RTLmachproof.v` are omitted here because the compilation pass form `RTL` to `RTLmach` was added in the `Stack-Aware-Nominal-CompCert` version.
For the 'Total' line, run again:
```
coqwc Nominal-CompCert/*/*.v
```
The first two numbers **in the last row of the output** are the results in row 'Total', column1 and column3 in Table2.

For the second and fourth columns(`Stack-Aware-Nominal-CompCert` version), copy and run:
```
coqwc Stack-Aware-Nominal-CompCert/common/Memory.v Stack-Aware-Nominal-CompCert/common/Globalenvs.v Stack-Aware-Nominal-CompCert/common/Events.v Stack-Aware-Nominal-CompCert/common/Separation.v Stack-Aware-Nominal-CompCert/backend/RTLmach.v Stack-Aware-Nominal-CompCert/backend/RTLmachproof.v Stack-Aware-Nominal-CompCert/cfrontend/SimplLocalsproof.v Stack-Aware-Nominal-CompCert/cfrontend/Cminorgenproof.v Stack-Aware-Nominal-CompCert/backend/Tailcallproof.v  Stack-Aware-Nominal-CompCert/backend/Inliningproof.v  Stack-Aware-Nominal-CompCert/backend/ValueAnalysis.v Stack-Aware-Nominal-CompCert/backend/Stackingproof.v
```
The first two columns of the output ('spec' and 'proof') respectively correspond to column2 and column4 in Table2. For the 'Total' line, run:
```
coqwc Stack-Aware-Nominal-CompCert/*/*.v
```
The first two numbers **in the last row of the output** correspond to the results in row 'Total', column1 and column3 in Table2.
### sudo password
There is no need to enter a password to run sudo in the virtual machine.
