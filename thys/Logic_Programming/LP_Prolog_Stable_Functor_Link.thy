theory LP_Prolog_Stable_Functor_Link
 imports LP_Prolog_Evaluation_Functor_Link LP_Prolog_Stable_Fresh_Context
begin

lemma lpp_functor_shape_context_stable:
 assumes observed: "lpp_stable_context_holds operation SP ctx eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) fs"
 shows "lpp_stable_context_holds operation SP (lpp_functor_shape_context ctx fs) eta"
proof -
 have "lpp_stable_observation_holds operation eta (lpp_functor_shape_observation f)"
   if "f\<in>set fs" for f
   using functors that by (cases f) (auto simp: list_all_iff intro: lpp_functor_argument_return_shape)
 then show ?thesis using observed
   by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff dest: lpp_stable_observation_refines)
qed

lemma lpp_stable_functor_link_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd ss G K eqs F source_context source_functors e"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
  shows "\<exists>nu. lpc_return_eval eta' ss=lpc_return_scope_word (lpcl_swaps e) (lpc_return_eval nu (states!lpcl_target e)) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target e))) (lpcn_guards (nds!lpcl_target e)) nu \<and>
    lpc_free_knowledge (set (Fs!lpcl_target e)) nu \<and>
    lpp_stable_context_holds operation SP (contexts!lpcl_target e) nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(lpcn_pred (nds!lpcl_target e),map nu (lpcn_vars (nds!lpcl_target e)))])\<in>lp_ild Q \<and>
    list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e)"
proof -
 have enriched: "lpp_stable_context_holds operation SP (lpp_functor_shape_context source_context source_functors) eta'"
  by (rule lpp_functor_shape_context_stable[OF observed functors])
 have base: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ss G K eqs F
    (lpp_functor_shape_context source_context source_functors) e"
  using checked by (simp add: lpp_check_evaluation_functor_link_def)
 have transported: "list_all (lpp_functor_fact_holds names
    (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings e) x) eta'))
    (functor_contexts!lpcl_target e)"
  by (rule lpp_check_functor_equation_transport_sound[where fuel=fuel, OF _ equations functors])
   (use checked in \<open>simp add: lpp_check_evaluation_functor_link_def\<close>)
 show ?thesis
  by (rule lpp_stable_link_witness_with_observation[where J="\<lambda>nu. list_all (lpp_functor_fact_holds names nu) (functor_contexts!lpcl_target e)",
    OF compatible program base equations old known free enriched transported])
qed

ML \<open>
val checked = [@{thm lpp_stable_functor_link_witness}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted stable functor link dependency" else ();
\<close>
end
