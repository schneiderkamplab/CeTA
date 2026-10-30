theory LP_Prolog_Context_Free_Equality
  imports LP_Cut_MGU_Unify_Free LP_Cut_Rational_Free_Equality LP_Prolog_Context_Refresh LP_Prolog_Context_Free_Link
begin

definition lpp_check_context_free_equality_node where
  "lpp_check_context_free_equality_node fuel P Q nds states contexts Fs nd F a b gs active saved k l next mode outputs source_context yes no =
    (lpc_check_free_equality_node fuel P Q nds nd F a b gs (map fst saved) k l next mode yes no \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lpc_return_short k saved \<and> lpp_context_short k source_context \<and>
       lpc_check_return_values fuel k (lpcn_ground nd)
         [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))]
         active (concat (map snd saved)) outputs \<and>
       lpp_check_context_free_link fuel Q nds states contexts Fs nd ((LPCGoals next,outputs)#saved) (lpcn_ground nd)
         (lpcn_guards nd@lpc_negative_guards k (set (lpcn_ground nd)) (lpcn_guards nd)@[LPCEqGuard a b True])
         [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd))) ] (lpc_unify_untouched_free F (lpcn_ground nd) a b gs k) (lpp_source_context_subst source_context (lp_cut_refresh k (set (lpcn_ground nd)))) yes) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
       lpp_check_context_free_link fuel Q nds states contexts Fs nd saved (lpcn_ground nd)
         (lpcn_guards nd@[LPCEqGuard a b False]) [] F source_context no))"

theorem lpp_context_free_equality_node_sound:
  assumes checked: "lpp_check_context_free_equality_node fuel P Q nds states contexts Fs nd F a b gs active saved k l next mode outputs source_context yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_free_rep SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
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
    using checked by (simp add: lpp_check_context_free_equality_node_def)
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
      and link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd ((LPCGoals next,outputs)#saved) ?G
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?eqs (lpc_unify_untouched_free F ?G a b gs k) (lpp_source_context_subst source_context (lp_cut_refresh k (set ?G))) yes"
      using checked possible by (auto simp: lpp_check_context_free_equality_node_def)
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
      using checked possible by (simp add: lpp_check_context_free_equality_node_def)
    have bounds: "2 * k \<le> l" using unify by (auto simp: lp_cut_check_unify_def)
    have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have facts: "lpp_source_context_holds SP
      (lpp_source_context_subst source_context (lp_cut_refresh k (set ?G))) ?env"
      by (rule lpp_context_refresh_sound[OF observed context_short bounds ground])
    have preserved: "lpc_free_knowledge (set (lpc_unify_untouched_free F ?G a b gs k)) ?env"
      by (rule lpc_unify_untouched_free_sound[OF mgu ground free bounds])
    show ?thesis using lpp_context_free_link_sound[OF link equations old knowledge preserved facts] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm.
        lp_isubst ?a sigma = lp_isubst ?b sigma)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      using lpc_free_equality_success coverage free failure by blast
    have link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd saved ?G (?K@[LPCEqGuard a b False]) [] F source_context no"
      using checked possible by (simp add: lpp_check_context_free_equality_node_def)
    have knowledge: "lp_cut_knowledge (set ?G) (?K@[LPCEqGuard a b False]) eta"
      using known failure by (simp add: lp_cut_knowledge_def)
    show ?thesis using lpp_context_free_link_sound[OF link _ refl knowledge free observed] failure
      by (simp add: lp_equations_def)
  qed
qed

ML \<open>
val checked = [@{thm lpp_context_free_equality_node_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source step dependency" else ();
\<close>
end
