As we mentioned in the paper, the `Stack-Aware-Nominal-CompCert` version extends the compilation chain of CompCert from `Asm.v` to `RealAsm.v`. We forgot to specify that the 'Total' results in Table2 was produced in a version without such extension. To get similar results here, you need to remove theses files under the directory 'x86':
```
AsmFacts.v AsmRegs.v SSAsm.v SSAsmproof.v RealAsm.v RealAsmgen.v RealAsmproof.v
```
Also this extension requires some specifications and lemmas in existing files, so the result here will be 145369 LOC, about 3400 LOC larger than the result in the paper.