theory LP_Prolog_Stable_Equality
 imports LP_Prolog_Stable_Resolution LP_Prolog_Evaluation_Equality
begin

lemma lpp_stable_context_with_equations_sound:
  assumes "lpp_stable_context_holds operation SP ctx eta" "lp_equations eqs eta"
  shows "lpp_stable_context_holds operation SP (lpp_context_with_equations ctx eqs) eta"
  using assms by (cases ctx)
    (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def lp_equations_def list_all_iff)

theorem lpp_stable_equality_node_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs nd F a b gs active saved k l next mode outputs source_context yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_stable_rep operation SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?b = "lp_ieval b eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have base: "lpc_check_free_equality_node fuel P Q nds nd F a b gs (map fst saved) k l next mode yes no"
    using checked by (simp add: lpp_check_evaluation_equality_node_def)
  have coverage: "lpc_check_free_equality fuel F a b mode"
    using base by (simp add: lpc_check_free_equality_node_def)
  have st: "lpc_answer_transition P ((LPCGoals (LPCUnify ?a ?b#?gs),?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma. lpc_mgu_unify ?a ?b ?gs sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_isubst ?b sigma))"
    using st by (cases rule: lpc_answer_transition.cases) auto
  from cases show ?thesis
  proof
    assume "\<exists>sigma. lpc_mgu_unify ?a ?b ?gs sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma where mgu: "lpc_mgu_unify ?a ?b ?gs sigma"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have eq: "lp_isubst ?a sigma = lp_isubst ?b sigma"
      using mgu by (simp add: lpc_mgu_unify_def)
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lpc_free_equality_failure coverage eq by blast
    have unify: "lp_cut_check_unify fuel k l ?G ?K a b gs (map fst saved) next"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_check_free_equality_node_def)
    have payload: "lpc_check_return_values fuel k ?G ?eqs active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpp_check_evaluation_link_free_choices T yes_facts fuel Q nds states contexts Fs nd ((LPCGoals next,outputs)#saved) ?G
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?eqs (lpc_unify_untouched_free F ?G a b gs k) (lpp_saved_free k F) (lpp_context_with_equations (lpp_evaluation_fork_context source_context k (set ?G)) ?eqs) yes"
      using checked possible by (auto simp: lpp_check_evaluation_equality_node_def)
    let ?env = "lp_cut_resolution_env k l eta sigma eta"
    have same: "tt=lpc_return_eval ?env ((LPCGoals next,outputs)#saved)"
      using result lpc_return_unification_success[OF unify known eq payload short]
      by (simp add: map_map o_def lp_cut_map_comp)
    have equations: "lp_equations ?eqs ?env" by (rule lp_cut_checked_unify_equations[OF unify known eq])
    have kl: "k\<le>l" using unify by (auto simp: lp_cut_check_unify_def)
    have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl parent])
    have prior: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b True]) ?env"
      by (rule lp_cut_checked_unify_success(2)[OF unify known eq])
    have negative: "list_all (\<lambda>g. lp_cut_guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule lpc_negative_guards_sound[OF _ _ known])
        (use unify in \<open>auto simp: lp_cut_check_unify_def\<close>)
    have knowledge: "lp_cut_knowledge (set ?G)
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?env"
      using prior negative by (simp add: lp_cut_knowledge_def)
    have context_short: "lpp_context_short k source_context"
      using checked possible by (simp add: lpp_check_evaluation_equality_node_def)
    have bounds: "2 * k \<le> l" using unify by (auto simp: lp_cut_check_unify_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have facts: "lpp_stable_context_holds operation SP
      (lpp_evaluation_fork_context source_context k (set ?G)) ?env"
      by (rule lpp_stable_context_fork_sound[OF observed context_short bounds ground])
    have initialized: "lpp_stable_context_holds operation SP
      (lpp_context_with_equations (lpp_evaluation_fork_context source_context k (set ?G)) ?eqs) ?env"
      by (rule lpp_stable_context_with_equations_sound[OF facts equations])
    have preserved: "lpc_free_knowledge (set (lpc_unify_untouched_free F ?G a b gs k)) ?env"
      by (rule lpc_unify_untouched_free_sound[OF mgu ground free bounds])
    have saved_free: "lpc_free_knowledge (set (lpp_saved_free k F)) ?env"
      by (rule lpp_saved_free_sound[OF free]) (use bounds in arith)
    show ?thesis using lpp_stable_link_free_choices_sound[OF compatible program link equations old knowledge preserved saved_free initialized] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_isubst ?b sigma)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lpc_free_equality_success coverage free failure by blast
    have link: "lpp_check_evaluation_link T no_facts fuel Q nds states contexts Fs nd saved ?G (?K@[LPCEqGuard a b False]) [] F source_context no"
      using checked possible by (simp add: lpp_check_evaluation_equality_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using lpp_stable_link_sound[OF compatible program link _ refl knowledge free observed] failure
      by (simp add: lp_equations_def)
  qed
qed

ML \<open>
val checked = [@{thm lpp_stable_context_with_equations_sound}, @{thm lpp_stable_equality_node_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable equality dependency" else ();
\<close>
end
