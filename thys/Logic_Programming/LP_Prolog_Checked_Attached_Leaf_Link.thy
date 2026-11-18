theory LP_Prolog_Checked_Attached_Leaf_Link
 imports LP_Prolog_Checked_Fresh_Univ_Step
begin

text \<open>The shared return-link checker equates whole annotated stacks,
including every payload. Caller leaf invariants therefore survive instance
transport without reinitializing them or merging saved environments. The
residual edge and child knowledge remain part of the checked result.\<close>

lemma lpp_checked_return_link_attached_leaf:
 assumes checked: "lpc_check_return_link fuel Q nds nd ss G guards eqs child e"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) guards eta'"
 defines "nu \<equiv> \<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'"
 shows "lpp_leaf_stack_invariant A specs (lpc_attach_answers rest (lpc_return_eval eta' ss)) =
   lpp_leaf_stack_invariant A specs (lpc_attach_answers rest (lpc_return_eval nu child))"
 and "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu"
 and "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
proof -
 have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu child)"
 and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu"
 and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
  using lpc_return_link_sound[OF checked equations old known] unfolding nu_def by blast+
 show "lpp_leaf_stack_invariant A specs (lpc_attach_answers rest (lpc_return_eval eta' ss)) =
   lpp_leaf_stack_invariant A specs (lpc_attach_answers rest (lpc_return_eval nu child))"
  by (simp only: lpp_leaf_stack_attachment same lpp_leaf_stack_scopes)
 show "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu"
  by (rule child_known)
 show "([(lpcn_pred nd,map eta (lpcn_vars nd))],
   [(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q"
  by (rule edge)
qed

ML \<open>
val checked = @{thms lpp_checked_return_link_attached_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked attached leaf link" else ();
\<close>
end
