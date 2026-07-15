#!/bin/bash
for i in *.proof.xml *.cpf.xml; do xmllint --huge --noout --schema ../xml/cpf3.xsd $i || echo $i >> error_validate.txt; done
