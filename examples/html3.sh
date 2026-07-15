#!/bin/bash
for i in *.proof.xml; do xsltproc --huge --stringparam alwaysExpandRuleIndices "false" ~/rewriting/examplesCPF3/cpf3HTML.xsl $i > ${i%.xml}.html; done
# for i in *.proof.xml; do xsltproc --huge ~/rewriting/examplesCPF3/cpf3HTML.xsl $i > ${i%.xml}.html; done
