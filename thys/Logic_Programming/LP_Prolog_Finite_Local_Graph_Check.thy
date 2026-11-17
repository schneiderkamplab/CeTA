theory LP_Prolog_Finite_Local_Graph_Check
 imports LP_Prolog_Finite_Local_Return_Families LP_Prolog_Finite_Local_Region_Descent
   LP_Prolog_Stable_Guarded_Graph
begin
hide_const (open) Tree_Automata_Containment.entry

fun lpp_check_finite_local_component where
  "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming_context entry (LPPFTRegion region) =
    lpp_check_finite_local_region A fuel P D Q T roots contexts incoming_context entry region (lppftr_contexts region)"
| "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming_context entry (LPPFTSplit first_types second_types receipt) =
    (lpp_finite_triple_check_preserved_split T first_types second_types fuel D Q roots contexts incoming_context entry receipt \<and>
      lpp_check_finite_return_goals A (lpcts_ground receipt @
        filter (\<lambda>x. x\<in>lpp_source_context_ground incoming_context) (lpcn_vars (lpctr_node entry)))
        (lpcts_rest receipt))"
| "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming_context entry (LPPFTIntegerSplit first_types second_types receipt evidence) =
    (lpp_finite_triple_check_integer_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence \<and>
      lpp_check_finite_return_goals A (lpcts_ground receipt @
        filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_integers incoming_context (lppsir_integers evidence))) (lpcn_vars (lpctr_node entry)))
        (lpcts_rest receipt))"

| "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming_context entry (LPPFTGroundSplit first_types second_types receipt evidence) =
    (lpp_finite_triple_check_ground_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence \<and>
      lpp_check_finite_return_goals A (lpcts_ground receipt @
        filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_ground incoming_context (lppsgr_ground evidence))) (lpcn_vars (lpctr_node entry)))
        (lpcts_rest receipt))"

| "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming_context entry (LPPFTShapeSplit first_types second_types receipt evidence) =
    (lpp_finite_triple_check_shape_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence \<and>
      lpp_check_finite_return_goals A (lpcts_ground receipt @
        filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_shape_receipt_context incoming_context evidence)) (lpcn_vars (lpctr_node entry)))
        (lpcts_rest receipt))"

definition lpp_check_finite_local_graph where
  "lpp_check_finite_local_graph A fuel P D Q T (roots::string lpc_triple_root list) contexts blocks q modes chain_pred OD descents =
    (lp_cut_source_program P \<and> (q,length modes)\<in>A \<and>
      (\<forall>(f,n)\<in>A. (f,n)\<in>lpp_builtin_signature \<longrightarrow> lpp_direct_arithmetic_name f) \<and>
      length descents=length roots \<and> roots\<noteq>[] \<and> length blocks=length roots \<and> length contexts=length roots \<and> contexts!0=([],[],[]) \<and>
      (let entry=roots!0; nd=lpctr_node entry; vs=lpcn_vars nd in
        lp_cut_check_root q modes vs (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd) \<and>
        lpctr_free entry=[] \<and> lpctr_input entry=(chain_pred,map Var vs)) \<and>
      list_all (\<lambda>i. lpp_check_finite_local_component A fuel P D Q T roots contexts (contexts!i) (roots!i) (blocks!i) \<and>
        lpp_check_finite_component_descent OD roots (contexts!i) (roots!i) (blocks!i) (descents!i))
        [0..<length roots])"

end
