theory LP_Cut_Domain_Projected_Residual
 imports Category_LP_Library.LP_Cut_Projected_XML Category_LP_Cut_Nested_Bridge.LP_Cut_Domain_Return_Nested_Triples
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

lemma precise_projected_return_link:
  fixes pi :: "'f lp_cut_symbol afs" and measure :: "('f lp_cut_symbol,string) term"
  assumes link: "lpc_check_return_link fuel Q nds nd ss H guards eqs child e"
    and checked: "lpc_check_projected_edge fuel k G A eqs
      (Fun (lpcn_pred nd) (map Var (lpcn_vars nd)))
      (Fun (lpcn_pred (nds!lpcl_target e))
        (map (lp_cut_instance_subst (lpcl_bindings e)) (lpcn_vars (nds!lpcl_target e))))
      left_term right_term"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and equations: "lp_equations eqs (lp_cut_resolution_env k l eta sigma rho)"
    and known: "knowledge (set H) guards (lp_cut_resolution_env k l eta sigma rho)"
    and observed: "lp_iproject pi (LPIFun (lpcn_pred nd) (map eta (lpcn_vars nd))) measure"
    and variables: "vars_term (af_term pi right_term) \<subseteq> vars_term (af_term pi left_term)"
    and rule: "(left_term,right_term)\<in>R"
  defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x)
    (lp_cut_resolution_env k l eta sigma rho)"
  obtains next_measure where
    "lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    "knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    "lp_iproject pi (LPIFun (lpcn_pred (nds!lpcl_target e))
      (map nu (lpcn_vars (nds!lpcl_target e)))) next_measure"
    "(measure,next_measure)\<in>rstep (af_rule pi ` R)"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  have same: "lpc_return_eval ?env ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    unfolding nu_def by (rule precise_return_link_sound(1)[OF link equations refl known])
  have knowledge: "knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    unfolding nu_def by (rule precise_return_link_sound(2)[OF link equations refl known])
  have pr: "lp_iproject pi (lp_ieval (Fun (lpcn_pred nd) (map Var (lpcn_vars nd))) eta) measure"
    using observed by (simp add: map_map o_def)
  obtain next_measure where projected: "lp_iproject pi
      (lp_ieval (Fun (lpcn_pred (nds!lpcl_target e))
        (map (lp_cut_instance_subst (lpcl_bindings e)) (lpcn_vars (nds!lpcl_target e)))) ?env)
      next_measure"
    and step: "(measure,next_measure)\<in>rstep (af_rule pi ` R)"
    by (rule lpc_checked_projected_edge[OF checked bounds ground equations pr variables rule])
  have child_pr: "lp_iproject pi (LPIFun (lpcn_pred (nds!lpcl_target e))
      (map nu (lpcn_vars (nds!lpcl_target e)))) next_measure"
    using projected by (simp add: nu_def map_map o_def)
  show thesis by (rule that[OF same knowledge child_pr step])
qed


end
end
