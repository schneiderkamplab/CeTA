theory LP_Prolog_Separation_Functor_Link
 imports LP_Prolog_Functor_Premised_Table
begin

text \<open>The ordinary checked graph link and explicit separation transport
share the same target and actual interface substitution. Both conditions hold
for the same valuation witness; unrelated existential witnesses cannot be joined.\<close>

lemma lpp_separation_functor_link_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
    and separation: "list_all (lpp_separation_holds eta') source_separation"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps (lpc_return_eval eta' ss)) u"
proof -
  let ?j="lpcl_target e"
  have enriched: "lpp_stable_context_holds operation SP (lpp_functor_shape_context source_context source_functors) eta'"
    by (rule lpp_functor_shape_context_stable[OF observed functors])
  have base: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F
    (lpp_functor_shape_context source_context source_functors) e"
    using checked by (simp add: lpp_check_evaluation_functor_link_def)
  have transported: "list_all (lpp_functor_fact_holds names
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')) (functor_contexts!?j)"
    by (rule lpp_check_functor_equation_transport_sound[where fuel=fuel, OF _ equations functors])
      (use checked in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
  have separated: "lpp_separation_node_conditions separation_contexts ?j
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta')"
    by (rule lpp_separation_node_transport[OF separation_bound separation_check separation])
  obtain nu where same: "lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!?j))"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!?j))) (lpcn_guards (nds!?j)) nu"
    and child_free: "lpc_free_knowledge (set (Fs!?j)) nu"
    and context_holds: "lpp_stable_context_holds operation SP (contexts!?j) nu"
    and child_separation: "lpp_separation_node_conditions separation_contexts ?j nu"
    and child_functors: "list_all (lpp_functor_fact_holds names nu) (functor_contexts!?j)"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))])\<in>lp_ild Q"
    using lpp_stable_link_witness_with_observation[where J="\<lambda>nu.
        list_all (lpp_functor_fact_holds names nu) (functor_contexts!?j) \<and>
        lpp_separation_node_conditions separation_contexts ?j nu",
      OF compatible program base equations old known free enriched conjI[OF transported separated]] by blast
  have bounds: "?j<length nds" "?j<length states" "?j<length contexts" "?j<length Fs" "?j<length functor_contexts"
    using checked by (auto simp: lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def
      lpc_check_return_link_def lpc_check_link_def)
  have inverse: "lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss)=lpc_return_eval nu (states!?j)"
    by (simp add: same lpc_return_scope_word_inverse)
  have rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
      (lpc_return_scope_word (rev (lpcl_swaps e)) (lpc_return_eval eta' ss))
      [(lpcn_pred (nds!?j),map nu (lpcn_vars (nds!?j)))]"
    unfolding lpp_premised_functor_rep_def
    by (rule exI[of _ ?j], rule exI[of _ nu]) (use bounds inverse knowledge child_free context_holds child_functors child_separation in auto)
  show ?thesis using edge rep by blast
qed

ML \<open>
val checked = @{thms lpp_separation_functor_link_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation functor link" else ();
\<close>
end
