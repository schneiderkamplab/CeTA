#!/bin/bash
# for i in *.proof.xml; do ../cpf2_to_3.sh --termIndex ../examples/$i > $i || echo $i >> error_convert.txt; done
for i in *.proof.xml; do ../cpf2_to_3.sh ../examples/$i > $i || echo $i >> error_convert.txt; done
