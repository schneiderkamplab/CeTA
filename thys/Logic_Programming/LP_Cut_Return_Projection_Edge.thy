theory LP_Cut_Return_Projection_Edge
  imports LP_Cut_Return_Continuation
begin

definition lpc_check_return_projection_edge where
  "lpc_check_return_projection_edge Q vs from_symbol to_symbol indices =
    (distinct vs \<and> list_all (\<lambda>i. i<length vs) indices \<and>
     ((from_symbol,map Var vs),[(to_symbol,map (\<lambda>i. Var (vs!i)) indices)])\<in>set Q)"

theorem lpc_return_projection_edge_sound:
  fixes vs :: "string list" and rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_return_projection_edge Q vs from_symbol to_symbol indices"
  shows "([(from_symbol,map rho [0..<length vs])],
    [(to_symbol,map (lpc_project_interface indices rho) [0..<length indices])])\<in>lp_ild Q"
proof -
  let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
  have distinct: "distinct vs" and bounds: "list_all (\<lambda>i. i<length vs) indices"
    and clause: "((from_symbol,map Var vs),[(to_symbol,map (\<lambda>i. Var (vs!i)) indices)])\<in>set Q"
    using checked by (auto simp: lpc_check_return_projection_edge_def)
  have tuple_values: "map ?nu vs=map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  have selected: "map (\<lambda>i. ?nu (vs!i)) indices=map rho indices"
    using bounds by (auto simp: list_all_iff intro!: map_cong lpc_return_tuple_valuation[OF distinct])
  have projected: "map (lpc_project_interface indices rho) [0..<length indices]=map rho indices"
    by (rule nth_equalityI) (auto simp: lpc_project_interface_def)
  have step: "([(from_symbol,map ?nu vs)],[(to_symbol,map (\<lambda>i. ?nu (vs!i)) indices)])\<in>lp_ild Q"
    using lp_seg_residual_step[OF clause, of "(from_symbol,map ?nu vs)" LPIVar ?nu "[]"]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
  show ?thesis using step by (simp add: tuple_values selected projected)
qed

end
