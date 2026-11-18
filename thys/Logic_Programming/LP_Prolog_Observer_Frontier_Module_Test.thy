theory LP_Prolog_Observer_Frontier_Module_Test
 imports LP_Prolog_Observer_Frontier_Module
begin

lemma lpp_frontier_module_missing_witness_rejected:
 "length witnesses\<noteq>length nds \<Longrightarrow>
  \<not>lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses"
 by (simp add: lpp_check_frontier_observer_module_def)

lemma lpp_frontier_module_missing_context_rejected:
 "length separation_contexts\<noteq>length nds \<Longrightarrow>
  \<not>lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses"
 by (simp add: lpp_check_frontier_observer_module_def)

lemma lpp_frontier_module_uncovered_row_rejected:
 assumes "i<length nds" "i\<in>frontier_nodes" "i\<notin>block_nodes" "actions!i=Some action"
 and "\<not>lpp_check_frontier_observer_local frontier_nodes P (nds!i) (contexts!i) separation_contexts i (states!i) action (witnesses!i)"
 shows "\<not>lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses"
 using assms by (auto simp: lpp_check_frontier_observer_module_def list_all_iff)

lemma lpp_frontier_module_preserves_shapes:
 "lpp_check_frontier_observer_module frontier_nodes block_nodes P nds states contexts separation_contexts actions witnesses \<Longrightarrow>
  lpp_check_observer_frontier_shapes frontier_nodes states"
 by (simp add: lpp_check_frontier_observer_module_def)

lemma lpp_frontier_local_univ_needs_block:
 "\<not>lpp_check_frontier_observer_local frontier_nodes P nd source_context separation_contexts i ss
   (LPPFUniv value_var name_var args_var middle facts) witness"
 by (simp add: lpp_check_frontier_observer_local_def)

end
