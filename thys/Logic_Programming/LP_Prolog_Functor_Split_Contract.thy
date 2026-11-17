theory LP_Prolog_Functor_Split_Contract
 imports LP_Prolog_Functor_Table_Contract LP_Prolog_Return_Interface LP_Cut_Return_Split_Check
begin

text \<open>The actual-return predicate H may carry finite observations, stable
  arithmetic and functor relations. It is a separate obligation from the prefix
  answer contract. Continuations need only cover actual successful returns.\<close>

lemma lpp_actual_return_preserves_functors:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame.
   list_all (lpp_functor_fact_holds names (snd frame)) observations) ss"
 shows "list_all (lpp_functor_fact_holds names eta) observations"
 by (rule lpp_actual_return_substitution_property[where
      F="\<lambda>rho. list_all (lpp_functor_fact_holds names rho) observations", OF _ actual initialized])
   (auto simp: list_all_iff intro: lpp_functor_fact_runtime_subst)

lemma lpp_actual_return_preserves_functor_interface:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and contexts: "list_all (\<lambda>frame. lpp_stable_context_holds operation SP ctx (snd frame)) ss"
 and functors: "list_all (\<lambda>frame. list_all (lpp_functor_fact_holds names (snd frame)) observations) ss"
 and spine: "list_all (\<lambda>frame. lpp_finite_spine cons nil (snd frame slot) n) ss"
 shows "lpp_stable_context_holds operation SP ctx eta \<and>
   list_all (lpp_functor_fact_holds names eta) observations \<and>
   lpp_finite_spine cons nil (eta slot) n"
 using lpp_stable_actual_return_preserves_context[OF actual contexts]
   lpp_actual_return_preserves_functors[OF actual functors]
   lpp_actual_return_preserves_spine[OF actual spine] by blast

theorem lpp_functor_split_actual_contract:
 fixes vs :: "string list"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes program: "lp_cut_source_program P"
 and shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
 and arity: "length indices=arity"
 and projection: "lpc_check_return_projection_edge Q vs continuation_returned returned indices"
 and prefix: "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) t prefix_return"
 and returns: "\<And>rho. lp_actual_answer
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow> H rho"
 and continuation: "\<And>rho. lp_actual_answer
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow> H rho \<Longrightarrow>
   lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
       (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)]
    (lp_ild Q) (prefix_return rho) (\<lambda>theta. [(continuation_returned,map theta [0..<length vs])])"
 shows "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta original) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
 let ?ss = "lpc_return_eval eta [(LPCGoals pre,interface)]"
 let ?cont = "\<lambda>rho. [(continuation_returned,map rho [0..<length vs])]"
 have composed: "lp_answer_contract ?T (lpc_attach_answers ?gs ?ss) (lp_ild Q) t ?cont"
  by (rule lpp_domain_contract_compose_actual[OF program prefix])
    (use continuation returns in \<open>auto simp: lpc_return_eval_def\<close>)
 have bridge: "(?cont rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
   for rho :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
 have projected: "lp_answer_contract ?T
   (lpc_reinterface (lpc_project_interface indices) (lpc_attach_answers ?gs ?ss))
   (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
  by (rule lpp_domain_contract_project[where F="lpc_project_interface indices",
       OF lpc_project_interface_commutes composed bridge])
 show ?thesis using projected lpc_return_split_shape_sound[OF shape, of eta] by simp
qed

ML \<open>
val checked = @{thms lpp_functor_split_actual_contract lpp_actual_return_preserves_functors lpp_actual_return_preserves_functor_interface};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor Split dependency" else ();
\<close>
end
