theory LP_Cut_Domain_Return_Equality
  imports LP_Cut_Domain_Return_Resolution
begin

context cut_runtime_domain
begin

theorem precise_return_equality_node_sound:
  assumes checked: "lpc_check_return_equality_node fuel P Q nds states nd a b gs active saved k l next mode outputs yes no"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "precise_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    precise_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  let ?G = "lpcn_ground nd"
  let ?K = "lpcn_guards nd"
  let ?a = "lp_ieval a eta"
  let ?b = "lp_ieval b eta"
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?ret = "lpc_return_env active eta"
  let ?eqs = "[(a\<cdot>lp_cut_refresh k (set ?G),b\<cdot>lp_cut_refresh k (set ?G))]"
  have base: "lpc_check_equality_node fuel P Q nds nd a b gs (map fst saved) k l next mode yes no"
    using checked by (simp add: lpc_check_return_equality_node_def)
  have coverage: "lp_cut_check_equality fuel a b mode"
    using base by (simp add: lpc_check_equality_node_def)
  have st: "precise_answer_transition P ((LPCGoals (LPCUnify ?a ?b#?gs),?ret)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  have cases: "(\<exists>sigma. (\<forall>x. D (sigma x)) \<and> lp_isubst ?a sigma = lp_isubst ?b sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved) \<or>
    (event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
        (\<forall>x. D (sigma x)) \<and> lp_isubst ?a sigma = lp_isubst ?b sigma))"
    using st by (cases rule: precise_answer_transition.cases) (auto simp: mgu_unify_def)
  from cases show ?thesis
  proof
    assume "\<exists>sigma. (\<forall>x. D (sigma x)) \<and> lp_isubst ?a sigma = lp_isubst ?b sigma \<and> event=None \<and>
      tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved"
    then obtain sigma where ds: "\<And>x. D (sigma x)" and eq: "lp_isubst ?a sigma = lp_isubst ?b sigma"
      and event: "event=None" and result: "tt=(LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs),
        (\<lambda>n. lp_isubst (?ret n) sigma))#?saved" by blast
    have possible: "mode\<noteq>LPCAlwaysFailure"
      using lp_cut_equality_failure coverage eq by blast
    have unify: "lp_cut_check_unify fuel k l ?G ?K a b gs (map fst saved) next"
      and parent: "\<forall>x\<in>set (lpcn_vars nd). length x<k"
      using base possible by (auto simp: lpc_check_equality_node_def)
    have payload: "lpc_check_return_values fuel k ?G ?eqs active (concat (map snd saved)) outputs"
      and short: "lpc_return_short k saved"
      and link: "lpc_check_return_table_link fuel Q nds states nd ((LPCGoals next,outputs)#saved) ?G
        (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?eqs yes"
      using checked possible by (auto simp: lpc_check_return_equality_node_def)
    let ?env = "lp_cut_resolution_env k l eta sigma eta"
    have same: "tt=lpc_return_eval ?env ((LPCGoals next,outputs)#saved)"
      using result precise_return_unification_success[OF unify known eq payload short ds]
      by (simp add: map_map o_def lp_cut_map_comp)
    have equations: "lp_equations ?eqs ?env" by (rule unify_equations[OF unify known eq])
    have kl: "k\<le>l" using unify by (auto simp: lp_cut_check_unify_def)
    have old: "map ?env (lpcn_vars nd)=map eta (lpcn_vars nd)"
      by (rule lp_cut_resolution_parent_interface[OF kl parent])
    have prior: "knowledge (set ?G) (?K@[LPCEqGuard a b True]) ?env"
      by (rule unify_success(2)[OF unify known eq ds])
    have negative: "list_all (\<lambda>g. guard_holds g ?env) (lpc_negative_guards k (set ?G) ?K)"
      by (rule negative_guards[OF _ _ known ds])
        (use unify in \<open>auto simp: lp_cut_check_unify_def\<close>)
    have knowledge: "knowledge (set ?G)
      (?K@lpc_negative_guards k (set ?G) ?K@[LPCEqGuard a b True]) ?env"
      using prior negative by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    show ?thesis using precise_return_table_link_sound[OF link equations old knowledge] event same by simp
  next
    assume failure: "event=None \<and> tt=?saved \<and>
      \<not>(\<exists>sigma::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
        (\<forall>x. D (sigma x)) \<and> lp_isubst ?a sigma = lp_isubst ?b sigma)"
    have possible: "mode\<noteq>LPCAlwaysSuccess"
      proof
      assume mode: "mode=LPCAlwaysSuccess"
      have "cut_domain_equality D a b eta" by (rule equality_success[OF coverage[unfolded mode]])
      then show False using failure by (simp add: cut_domain_equality_def)
    qed
    have link: "lpc_check_return_table_link fuel Q nds states nd saved ?G (?K@[LPCEqGuard a b False]) [] no"
      using checked possible by (simp add: lpc_check_return_equality_node_def)
    have knowledge: "knowledge (set ?G) (?K@[LPCEqGuard a b False]) eta"
      using known failure by (simp add: knowledge_def cut_domain_head_def cut_domain_equality_def)
    show ?thesis using precise_return_table_link_sound[OF link _ refl knowledge] failure
      by (simp add: lp_equations_def)
  qed
qed

end
end
