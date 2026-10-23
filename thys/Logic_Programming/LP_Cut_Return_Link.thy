theory LP_Cut_Return_Link
  imports LP_Cut_Return_State LP_Cut_Table_Link
begin

definition lpc_return_map where
  "lpc_return_map f ss = map (\<lambda>(e,ts). (lp_cut_entry_map f e,map f ts)) ss"

fun lpc_return_scope_word where
  "lpc_return_scope_word [] ss = ss"
| "lpc_return_scope_word ((a,b)#swaps) ss = lpc_return_scope_word swaps
    (map (map_prod (lp_cut_scope_entry (lp_cut_scope_swap a b)) id) ss)"

lemma lpc_return_eval_subst:
  "lpc_return_eval eta (lpc_return_map (\<lambda>t. t\<cdot>mu) ss) =
    lpc_return_eval (\<lambda>x. lp_ieval (mu x) eta) ss"
proof -
  have env: "lpc_return_env (map (\<lambda>t. t\<cdot>mu) ts) eta =
    lpc_return_env ts (\<lambda>x. lp_ieval (mu x) eta)" for ts
    by (rule lpc_return_env_cong) (simp add: map_map o_def lp_ieval_finite_subst)
  show ?thesis
    by (simp add: lpc_return_eval_def lpc_return_map_def map_map o_def split_def
      lp_cut_entry_eval_subst env)
qed

lemma lpc_return_eval_scopes:
  "lpc_return_eval eta (lpc_return_scope_word swaps ss) =
    lpc_return_scope_word swaps (lpc_return_eval eta ss)"
  by (induct swaps arbitrary: ss)
    (auto simp: lpc_return_eval_def map_map o_def split_def map_prod_def
      lp_cut_scope_entry_map split: prod.splits)

definition lpc_check_return_link where
  "lpc_check_return_link fuel Q nds nd ss G guards eqs child e =
    (lpc_check_link fuel Q nds nd (map fst ss) G guards eqs e \<and>
     map fst child = lpcn_state (nds!lpcl_target e) \<and>
     lpc_return_map (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))) ss =
       lpc_return_scope_word (lpcl_swaps e)
         (lpc_return_map (\<lambda>t. t\<cdot>lp_cut_instance_subst (lpcl_bindings e)) child))"

text \<open>The receipt equates the whole annotated stack, not just its erased
goals. Consequently an alias cannot silently forget answer-only variables or
merge outputs whose live source states happen to agree.\<close>

theorem lpc_return_link_sound:
  assumes checked: "lpc_check_return_link fuel Q nds nd ss G guards eqs child e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd) = map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) guards eta'"
  defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
  shows "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    and "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e)))
      (lpcn_guards (nds!lpcl_target e)) nu"
    and "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
proof -
  let ?mu = "lp_cut_instance_subst (lpcl_bindings e)"
  let ?target = "nds!lpcl_target e"
  have link: "lpc_check_link fuel Q nds nd (map fst ss) G guards eqs e"
    and annotated: "lpc_return_map
      (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))) ss =
      lpc_return_scope_word (lpcl_swaps e) (lpc_return_map (\<lambda>t. t\<cdot>?mu) child)"
    using checked by (auto simp: lpc_check_return_link_def)
  have intf: "lp_cut_check_interface fuel eqs (lpcl_vars e) (lpcl_terms e) (map fst ss) G guards
      (lpcl_state e) (lpcl_ground e) (lpcl_guards e)"
    and inst: "lp_cut_check_instance (lpcl_state e) (lpcl_ground e) (lpcl_guards e)
      (lpcn_state ?target) (lpcn_ground ?target) (lpcn_guards ?target) (lpcl_bindings e) (lpcl_swaps e)"
    and lhs: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcn_vars nd)) =
      Some (Some (map LPCAtom (lpcl_lhs e)))"
    and rhs: "lp_cut_normalize fuel eqs (map LPCAtom (map ?mu (lpcn_vars ?target))) =
      Some (Some (map LPCAtom (lpcl_rhs e)))"
    and clause: "((lpcn_pred nd,lpcl_lhs e),[(lpcn_pred ?target,lpcl_rhs e)])\<in>set Q"
    using link by (auto simp: lpc_check_link_def Let_def)
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) (lpcl_vars e)) =
    Some (Some (map LPCAtom (lpcl_terms e)))"
    using intf by (simp add: lp_cut_check_interface_def)
  have unchanged: "\<And>x. lp_ieval (lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e)) x) eta' = eta' x"
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have evaluated: "lpc_return_eval eta'
      (lpc_return_map (\<lambda>t. t\<cdot>lp_cut_instance_subst (zip (lpcl_vars e) (lpcl_terms e))) ss) =
      lpc_return_eval eta' (lpc_return_scope_word (lpcl_swaps e) (lpc_return_map (\<lambda>t. t\<cdot>?mu) child))"
    by (rule arg_cong[OF annotated])
  show "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
    using evaluated by (simp add: lpc_return_eval_subst lpc_return_eval_scopes unchanged nu_def)
  have specialized: "lp_cut_knowledge (set (lpcl_ground e)) (lpcl_guards e) eta'"
    by (rule lp_cut_checked_interface_knowledge[OF intf equations known])
  show "lp_cut_knowledge (set (lpcn_ground ?target)) (lpcn_guards ?target) nu"
    unfolding nu_def by (rule lp_cut_checked_instance_knowledge[OF inst specialized])
  have normalized_rhs: "map (\<lambda>t. lp_ieval t eta') (lpcl_rhs e)=map nu (lpcn_vars ?target)"
    using lp_cut_normalized_terms[OF equations rhs] by (simp add: nu_def map_map o_def)
  show "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred ?target,map nu (lpcn_vars ?target))])\<in>lp_ild Q"
    using lp_cut_normalized_residual_step[OF clause equations lhs old] normalized_rhs by simp
qed

end
