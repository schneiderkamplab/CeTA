#!/bin/bash
for i in *.proof.xml; do echo -n "$i: "; ../build/ceta $i || echo $i >> error_cert.txt; done
../build/ceta --inputf div.input.xml --propertyf div.property --answerf div.answer div.cpf.xml 
