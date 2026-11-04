theory LP_Cut_Rational_NO_Control
  imports LP_Cut_Rational_NO_Steps LP_Cut_Allocate
begin

definition lpc_rational_case where
  "lpc_rational_case G P i gs es m successor =
    (i<length G \<and> lp_cut_fresh m (LPCGoals (LPCAtom i#gs)#es) \<and>
     (case G!i of LPRBranch (LPCUser f) js \<Rightarrow>
       successor=map (\<lambda>c. LPCClause (LPCAtom i#gs) c m)
         (lp_cut_slice P (LPCUser f) (length js)) @ LPCBarrier m#es
      | _ \<Rightarrow> False))"

lemma lpc_rational_case_sound:
  assumes checked: "lpc_rational_case G P i gs es m successor"
  shows "(lpc_rational_state G (LPCGoals (LPCAtom i#gs)#es),
    lpc_rational_state G successor)\<in>lp_cut_mgu_source P"
proof -
  obtain f js where branch: "G!i=LPRBranch (LPCUser f) js"
    using checked by (auto simp: lpc_rational_case_def split: lp_rational_node.splits lp_cut_symbol.splits)
  have index: "i<length G" and fresh: "lp_cut_fresh m (LPCGoals (LPCAtom i#gs)#es)"
    using checked by (auto simp: lpc_rational_case_def)
  have evaluated: "lp_rational_graph_value G LPIVar i =
    LPIFun (LPCUser f) (map (lp_rational_graph_value G LPIVar) js)"
    by (rule lp_rational_graph_branch[OF lp_rational_graph_value_model index branch])
  have fresh_eval: "lp_cut_fresh m (lpc_rational_state G (LPCGoals (LPCAtom i#gs)#es))"
    using fresh by simp
  show ?thesis using lp_cut_mgu_source.case_call[of m f
    "map (lp_rational_graph_value G LPIVar) js"
    "map (lp_cut_map (lp_rational_graph_value G LPIVar)) gs" "lpc_rational_state G es" P]
    fresh_eval checked
    by (simp add: lpc_rational_case_def branch evaluated lp_cut_state_map_def map_map o_def)
qed

lemma lpc_rational_admin_sound:
  "lp_cut_admin s=Some t \<Longrightarrow>
    (lpc_rational_state G s,lpc_rational_state G t)\<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.admin) (simp add: lp_cut_admin_map)

end
