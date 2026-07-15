for i in Proof_Checker/Check_Nontermination.thy; do sed -i -e "s/shows \(''[^']*''\)/showsl_lit (STR \1)/g" $i; sed -i -e "s/shows_string \(''[^']*''\)/showsl_lit (STR \1)/g" $i; sed -i -e "s/shows check/showsl check/g" $i; sed -i -e "s/shows_/showsl_/g" $i; sed -i -e "s/:: *show/:: showl/g" $i; sed -i -e "s/shows \([a-zA-Z]\)/showsl \1/g" $i; sed -i -e "s/show, *compare_order/showl, compare_order/g" $i; sed -i -e "s/compare_order, *show/showl, compare_order/g" $i; done


sed -i -e "s/debug i \(''[^']*''\)/debug i (STR \1)/g" Proof_Checker/Check_Nontermination.thy
