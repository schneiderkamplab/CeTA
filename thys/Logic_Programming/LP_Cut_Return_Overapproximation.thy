theory LP_Cut_Return_Overapproximation
 imports LP_Cut_Return_Independent_Certificate
begin

definition lpc_check_universal_return_edge where
  "lpc_check_universal_return_edge Q nd returned arity outputs =
    (length outputs=arity \<and> distinct outputs \<and>
     set outputs\<inter>set (lpcn_vars nd)={} \<and>
     ((lpcn_pred nd,map Var (lpcn_vars nd)),[(returned,map Var outputs)])\<in>set Q)"

lemma lpc_universal_return_edge_sound:
  fixes rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_check_universal_return_edge Q nd returned arity outputs"
  shows "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>lp_ild Q"
proof -
  let ?out = "lp_cut_query_env outputs (map rho [0..<arity])"
  let ?nu = "\<lambda>x. if x\<in>set (lpcn_vars nd) then eta x else ?out x"
  have len: "length outputs=arity" and distinct: "distinct outputs"
    and disjoint: "set outputs\<inter>set (lpcn_vars nd)={}"
    and clause: "((lpcn_pred nd,map Var (lpcn_vars nd)),[(returned,map Var outputs)])\<in>set Q"
    using checked by (auto simp: lpc_check_universal_return_edge_def)
  have inputs: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)" by auto
  have out: "map ?out outputs=map rho [0..<arity]"
    by (rule lp_cut_query_env_values) (use len distinct in auto)
  have outputs: "map ?nu outputs=map rho [0..<arity]"
  proof -
    have "map ?nu outputs=map ?out outputs" using disjoint by (auto intro!: map_cong)
    then show ?thesis using out by simp
  qed
  have step: "([(lpcn_pred nd,map ?nu (lpcn_vars nd))],[(returned,map ?nu outputs)])\<in>lp_ild Q"
    using lp_seg_residual_step[OF clause, of "(lpcn_pred nd,map ?nu (lpcn_vars nd))" LPIVar ?nu "[]"]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def o_def)
  show ?thesis using step inputs outputs by simp
qed

theorem lpc_independent_return_contract:
  assumes checked: "lpc_check_universal_return_edge Q nd returned arity outputs"
    and source: "SN_on (lp_cut_mgu_source P) {map fst (lpc_return_eval eta original)}"
  shows "lpc_return_contract P (lpc_return_eval eta original) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  using source lpc_universal_return_edge_sound[OF checked, of eta]
  by (auto simp: lpc_return_contract_def intro: r_into_rtrancl)

end
