theory LP_Cut_Projected_Residual
  imports LP_Cut_Return_Projection LP_Cut_Return_Link
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

text \<open>A projected residual edge is a separate obligation from an ordinary
return-table edge. It normalizes the refreshed active observations, leaves saved
observations untouched, and checks the filtered variable condition. It does not
assert equality of the original runtime values and cannot be used as an
unconditional ordinary-LP edge. Source transition coverage and graph closure
remain obligations of the enclosing certificate.\<close>

definition lpc_check_projected_edge where
  "lpc_check_projected_edge fuel k G A eqs src dst left_term right_term =
    ((\<forall>x\<in>vars_term src. length x<k) \<and>
     lp_cut_normalize fuel eqs
       [LPCAtom (src\<cdot>lpc_observation_refresh k (set G) (set A))] =
         Some (Some [LPCAtom left_term]) \<and>
     lp_cut_normalize fuel eqs [LPCAtom dst] = Some (Some [LPCAtom right_term]))"

lemma lpc_checked_projected_edge:
  fixes pi :: "'f afs" and measure :: "('f,string) term"
  assumes checked: "lpc_check_projected_edge fuel k G A eqs src dst left_term right_term"
    and bounds: "2 * k \<le> l"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and equations: "lp_equations eqs (lp_cut_resolution_env k l eta sigma rho)"
    and observed: "lp_iproject pi (lp_ieval src eta) measure"
    and variables: "vars_term (af_term pi right_term) \<subseteq> vars_term (af_term pi left_term)"
    and rule: "(left_term,right_term)\<in>R"
  obtains next_measure where
    "lp_iproject pi (lp_ieval dst (lp_cut_resolution_env k l eta sigma rho)) next_measure"
    "(measure,next_measure)\<in>rstep (af_rule pi ` R)"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  let ?input = "src\<cdot>lpc_observation_refresh k (set G) (set A)"
  have short: "\<forall>x\<in>vars_term src. length x<k"
    and norm_in: "lp_cut_normalize fuel eqs [LPCAtom ?input] = Some (Some [LPCAtom left_term])"
    and norm_out: "lp_cut_normalize fuel eqs [LPCAtom dst] = Some (Some [LPCAtom right_term])"
    using checked by (auto simp: lpc_check_projected_edge_def)
  have input_eq: "lp_ieval left_term ?env = lp_ieval ?input ?env"
    using lp_cut_normalized_terms[OF equations, of fuel "[?input]" "[left_term]"] norm_in by simp
  have output_eq: "lp_ieval right_term ?env = lp_ieval dst ?env"
    using lp_cut_normalized_terms[OF equations, of fuel "[dst]" "[right_term]"] norm_out by simp
  have pr: "lp_iproject pi (lp_ieval left_term ?env) measure"
    unfolding input_eq
    by (rule lpc_resolution_projected_observation[OF observed short bounds ground])
  obtain next_measure where projected: "lp_iproject pi (lp_ieval right_term ?env) next_measure"
    and step: "(measure,next_measure)\<in>rstep (af_rule pi ` R)"
    by (rule lp_infinite_rule_projection[OF pr variables rule])
  show thesis by (rule that[OF _ step]) (use projected output_eq in simp)
qed

text \<open>Connect the projected step to the checked whole-stack return link.
The auxiliary ordinary helper clause is used only to check state/answer
matching. Its termination is not assumed. Progress comes from the projected
rule and its variable condition, while all guards and saved answers survive.\<close>

lemma lpc_projected_return_link:
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
    and known: "lp_cut_knowledge (set H) guards (lp_cut_resolution_env k l eta sigma rho)"
    and observed: "lp_iproject pi (LPIFun (lpcn_pred nd) (map eta (lpcn_vars nd))) measure"
    and variables: "vars_term (af_term pi right_term) \<subseteq> vars_term (af_term pi left_term)"
    and rule: "(left_term,right_term)\<in>R"
  defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x)
    (lp_cut_resolution_env k l eta sigma rho)"
  obtains next_measure where
    "lpc_return_eval (lp_cut_resolution_env k l eta sigma rho) ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    "lp_iproject pi (LPIFun (lpcn_pred (nds!lpcl_target e))
      (map nu (lpcn_vars (nds!lpcl_target e)))) next_measure"
    "(measure,next_measure)\<in>rstep (af_rule pi ` R)"
proof -
  let ?env = "lp_cut_resolution_env k l eta sigma rho"
  have same: "lpc_return_eval ?env ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    unfolding nu_def by (rule lpc_return_link_sound(1)[OF link equations refl known])
  have knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    unfolding nu_def by (rule lpc_return_link_sound(2)[OF link equations refl known])
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
