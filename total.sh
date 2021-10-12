coqwc CompCert-3.8/*/*.v > coqwc_1.txt
coqwc Nominal-CompCert/*/*.v > coqwc_2.txt
coqwc Stack-Aware-Nominal-CompCert/*/*.v > coqwc_3.txt
echo 'CompCert-3.8:'
echo $(head -n 1 coqwc_1.txt)
echo $(tail -n 1 coqwc_1.txt)
echo 'Nominal-CompCert:'
echo $(head -n 1 coqwc_2.txt)
echo $(tail -n 1 coqwc_2.txt)
echo 'Stack-Aware-Nominal-CompCert:'
echo $(head -n 1 coqwc_3.txt)
echo $(tail -n 1 coqwc_3.txt)
rm coqwc_1.txt coqwc_2.txt coqwc_3.txt
