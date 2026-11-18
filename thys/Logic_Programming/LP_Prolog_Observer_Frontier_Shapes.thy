theory LP_Prolog_Observer_Frontier_Shapes
 imports LP_Prolog_Observer_Frontier_Table
begin

definition lpp_observer_internal_frame where
 "lpp_observer_internal_frame ss = (lpp_observer_equality_frame ss \<or> lpp_observer_univ_frame ss)"

fun lpp_observer_template_internal_frame where
 "lpp_observer_template_internal_frame ((LPCGoals (LPCUnify a b#gs),env)#saved) = True"
| "lpp_observer_template_internal_frame ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),env)#saved) = (f=''2:=..'')"
| "lpp_observer_template_internal_frame ss = False"

lemma lpp_observer_template_internal_sound:
 assumes "lpp_observer_template_internal_frame ss"
 shows "lpp_observer_internal_frame (lpc_return_eval eta ss)"
 using assms by (induction ss rule: lpp_observer_template_internal_frame.induct)
  (auto simp: lpp_observer_internal_frame_def lpc_return_eval_def)

lemma lpp_observer_internal_scopes:
 "lpp_observer_internal_frame (lpc_return_scope_word swaps ss)=lpp_observer_internal_frame ss"
 by (simp add: lpp_observer_internal_frame_def lpp_observer_equality_frame_scopes lpp_observer_univ_frame_scopes)

definition lpp_check_observer_frontier_shapes where
 "lpp_check_observer_frontier_shapes frontier_nodes states =
  list_all (\<lambda>i. i\<in>frontier_nodes \<or> lpp_observer_template_internal_frame (states!i)) [0..<length states]"

lemma lpp_observer_exit_frontier_rep:
 assumes checked: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts base_conditions ss t"
 and exit_shape: "\<not>lpp_observer_internal_frame ss"
 shows "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes base_conditions) ss t"
proof -
 obtain swaps i eta where bounds: "i<length nds" "i<length states" "i<length contexts" "i<length Fs" "i<length functor_contexts"
 and conditions: "base_conditions i eta"
 and exact: "lpc_return_scope_word swaps ss=lpc_return_eval eta (states!i)"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and subject: "t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
  using represented by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
 have member: "i\<in>frontier_nodes"
 proof (rule ccontr)
  assume "i\<notin>frontier_nodes"
  then have internal: "lpp_observer_template_internal_frame (states!i)"
   using checked bounds(2) by (auto simp: lpp_check_observer_frontier_shapes_def list_all_iff)
  have "lpp_observer_internal_frame (lpc_return_scope_word swaps ss)"
   using lpp_observer_template_internal_sound[OF internal, of eta] exact by simp
  then show False using exit_shape by (simp add: lpp_observer_internal_scopes)
 qed
 show ?thesis unfolding lpp_premised_functor_module_rep_def
  apply (rule exI[of _ swaps])
  using bounds conditions exact known free observed functors subject member
  by (auto simp: lpp_premised_functor_rep_def lpp_observer_frontier_conditions_def)
qed

lemma lpp_observer_empty_frontier_has_no_rep:
 "\<not>lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions {} base_conditions) ss t"
 by (simp add: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def lpp_observer_frontier_conditions_def)

lemma lpp_observer_external_row_cannot_be_hidden:
 assumes "i<length states" "\<not>lpp_observer_template_internal_frame (states!i)" "i\<notin>frontier_nodes"
 shows "\<not>lpp_check_observer_frontier_shapes frontier_nodes states"
 using assms by (auto simp: lpp_check_observer_frontier_shapes_def list_all_iff)

ML \<open>
val checked = @{thms lpp_observer_template_internal_sound lpp_observer_internal_scopes lpp_observer_exit_frontier_rep
 lpp_observer_empty_frontier_has_no_rep lpp_observer_external_row_cannot_be_hidden};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted observer frontier shapes" else ();
\<close>
end
