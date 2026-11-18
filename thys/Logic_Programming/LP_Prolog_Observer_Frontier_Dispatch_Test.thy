theory LP_Prolog_Observer_Frontier_Dispatch_Test
 imports LP_Prolog_Observer_Frontier_Ordinary_Check
 LP_Prolog_Observer_Frontier_Fresh_Check
 LP_Prolog_Observer_Frontier_Ground_Equality_Check
begin

lemma lpp_frontier_missing_destination_rejected:
 "lpcl_target e\<notin>frontier_nodes \<Longrightarrow>
  \<not>lpp_check_frontier_observer_target frontier_nodes separation_contexts i e"
 by (simp add: lpp_check_frontier_observer_target_def)

lemma lpp_frontier_missing_context_rejected:
 "lpcl_target e\<ge>length separation_contexts \<Longrightarrow>
  \<not>lpp_check_frontier_observer_target frontier_nodes separation_contexts i e"
 by (simp add: lpp_check_frontier_observer_target_def)

lemma lpp_frontier_failed_transport_rejected:
 "\<not>lpp_check_separation_transport (separation_contexts!i)
   (separation_contexts!lpcl_target e) (lp_cut_instance_subst (lpcl_bindings e)) \<Longrightarrow>
  \<not>lpp_check_frontier_observer_target frontier_nodes separation_contexts i e"
 by (simp add: lpp_check_frontier_observer_target_def)

lemma lpp_frontier_parallel_missing_child_rejected:
 "e\<in>set links \<Longrightarrow> lpcl_target e\<notin>frontier_nodes \<Longrightarrow>
  \<not>lpp_check_frontier_observer_ordinary frontier_nodes separation_contexts i ss
    (LPPFParallel links factss)"
 by (auto simp: list_all_iff lpp_check_frontier_observer_target_def)

lemma lpp_frontier_parallel_missing_frame_rejected:
 "length links\<noteq>length ss \<Longrightarrow>
  \<not>lpp_check_frontier_observer_ordinary frontier_nodes separation_contexts i ss
    (LPPFParallel links factss)"
 by simp

lemma lpp_frontier_target_checked:
 "lpcl_target e\<in>frontier_nodes \<Longrightarrow> i<length separation_contexts \<Longrightarrow>
  lpcl_target e<length separation_contexts \<Longrightarrow>
  lpp_check_separation_transport (separation_contexts!i)
   (separation_contexts!lpcl_target e) (lp_cut_instance_subst (lpcl_bindings e)) \<Longrightarrow>
  lpp_check_frontier_observer_target frontier_nodes separation_contexts i e"
 by (simp add: lpp_check_frontier_observer_target_def)

end
