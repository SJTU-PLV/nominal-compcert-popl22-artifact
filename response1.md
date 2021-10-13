First and foremost, we don't think there is a password for sudo. Could the reviewer check it again and let us know if there is any problem with sudo?

The following are the instructions for reproducing the results in Table 1 and 2. Note that we continued to work on this artifact after we submitted the paper. Therefore, some results are slightly different from those in the paper.

All the commands in the following instructions should be executed under the directory 'nominal-compcert-popl22-artifact'.

## Table 1

### Column 2
The results in the second column can be produced by running:

```
coqwc CompCert-3.8/common/Values.v CompCert-3.8/common/Memory.v CompCert-3.8/common/Memtype.v CompCert-3.8/common/Globalenvs.v CompCert-3.8/cfrontend/SimplLocalsproof.v CompCert-3.8/cfrontend/Cminorgenproof.v CompCert-3.8/backend/Inliningproof.v  CompCert-3.8/backend/ValueAnalysis.v CompCert-3.8/backend/Unusedglobproof.v
```

This command lists the lines of code (LOC) for files in CompCert 3.8 that also appear in the Table 1 in three categories: 'spec', 'proof' and 'comments'. The numbers in column 2 are obtained by adding the numbers in 'spec' and 'proof' for each file. 

The number at the row 'Total' is the summation of LOC for all coq files(.v). It is obtained by running:
```
coqwc CompCert-3.8/*/*.v
```
and adding the numbers in the 'spec' and 'proof' categories in the last line.

### Column 3
The numbers in column 3 can be obtained in a similar way. Run the following command:
```
coqwc Nominal-CompCert/common/Values.v Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Memtype.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Unusedglobproof.v
```
and add the numbers in 'spec' and 'proof' to get the results in column 3. For the result at the row 'Total', run
```
coqwc Nominal-CompCert/*/*.v
```
and add the numbers in 'spec' and 'proof' in the last line.

### Column 4
The results in the fourth column were manually collected from the [github compare page](https://github.com/SJTU-PLV/CompCert/compare/478ece4...e9c10d5). For each file, the number is the bigger one among "additions" and "deletions", with the number of empty lines subtracted. 

### Column 5
The last column contains the ratios of the numbers in column 4 to those in column 2.


## Table 2

In Table 2, we list the LOC for 'spec' and 'proof' separately. For the second and fourth columns(`Nominal-CompCert`), run:
```
coqwc Nominal-CompCert/common/Memory.v Nominal-CompCert/common/Globalenvs.v Nominal-CompCert/common/Events.v Nominal-CompCert/common/Separation.v Nominal-CompCert/cfrontend/SimplLocalsproof.v Nominal-CompCert/cfrontend/Cminorgenproof.v Nominal-CompCert/backend/Tailcallproof.v  Nominal-CompCert/backend/Inliningproof.v  Nominal-CompCert/backend/ValueAnalysis.v Nominal-CompCert/backend/Stackingproof.v
```
The results in the 'spec' and 'proof' categories correspond to column 2 and column 4, respectively. The `RTLmach.v` and `RTLmachproof.v` are omitted here because the compilation pass form `RTL` to `RTLmach` was only added to `Stack-Aware-Nominal-CompCert`.

For the row 'Total', run:
```
coqwc Nominal-CompCert/*/*.v
```
Again, the first two numbers in the last line correspond to the results at row 'Total' in column 2 and column 4.

For the third and fifth columns(`Stack-Aware-Nominal-CompCert`), run:
```
coqwc Stack-Aware-Nominal-CompCert/common/Memory.v Stack-Aware-Nominal-CompCert/common/Globalenvs.v Stack-Aware-Nominal-CompCert/common/Events.v Stack-Aware-Nominal-CompCert/common/Separation.v Stack-Aware-Nominal-CompCert/backend/RTLmach.v Stack-Aware-Nominal-CompCert/backend/RTLmachproof.v Stack-Aware-Nominal-CompCert/cfrontend/SimplLocalsproof.v Stack-Aware-Nominal-CompCert/cfrontend/Cminorgenproof.v Stack-Aware-Nominal-CompCert/backend/Tailcallproof.v  Stack-Aware-Nominal-CompCert/backend/Inliningproof.v  Stack-Aware-Nominal-CompCert/backend/ValueAnalysis.v Stack-Aware-Nominal-CompCert/backend/Stackingproof.v
```
The 'spec' and 'proof' categories of the output correspond to column 3 and column 5. The numbers are higher because we continued working on Stack-Aware Nominal CompCert for a while after submission.

The numbers at the row 'Total' in column 3 and 5 are obtained like before, by running:
```
coqwc Stack-Aware-Nominal-CompCert/*/*.v
```
