theory LP_Prolog_Evaluation_Probe
  imports LP_Prolog_Finite_Probe LP_Prolog_Evaluation_Allocate
begin

lemma lpp_probe_stack_eval:
  "lpc_return_eval eta (lpp_probe_stack a keep m n gs active saved) =
    lpp_probe_stack (lp_ieval a eta) keep m n
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
      (lpc_return_env active eta) (lpc_return_eval eta saved)"
  by (cases keep)
    (simp_all add: lpc_return_eval_def lpp_probe_stack_def lpp_probe_goals_def lpp_probe_else_def)

lemma lpp_probe_checked_covers:
  assumes name: "lpp_probe_name f"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>swaps. tt=lpc_return_scope_word swaps
    (lpc_return_eval eta (lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs active saved)))"
proof -
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?a = "lp_ieval (Fun (LPCUser g) argv) eta"
  let ?active = "lpc_return_env active eta"
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [LPIFun (LPCUser g) (map (\<lambda>t. lp_ieval t eta) argv)])#?gs),?active)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  obtain k l where event: "event=None"
    and fk: "lp_cut_fresh k (LPCGoals ?gs#map fst ?saved)"
    and fl: "lp_cut_fresh l (LPCBarrier k#LPCGoals ?gs#map fst ?saved)"
    and target: "tt=lpp_probe_stack ?a (f=''1:once'') k l ?gs ?active ?saved"
    using lpp_finite_probe_step[OF name actual] by auto
  have em: "lp_cut_fresh m (LPCGoals ?gs#map fst ?saved)"
    using fm lp_cut_fresh_state_map[of m "\<lambda>t. lp_ieval t eta" "LPCGoals gs#map fst saved"]
    by (simp add: lpc_return_eval_erases lp_cut_state_map_def)
  have en: "lp_cut_fresh n (LPCGoals ?gs#map fst ?saved)"
    using fn lp_cut_fresh_state_map[of n "\<lambda>t. lp_ieval t eta" "LPCGoals gs#map fst saved"]
    by (simp add: lpc_return_eval_erases lp_cut_state_map_def lp_cut_fresh_def)
  have el: "lp_cut_fresh l (LPCGoals ?gs#map fst ?saved)"
    and kl: "k\<noteq>l" using fl by (auto simp: lp_cut_fresh_def)
  have mn: "m\<noteq>n" using fn by (auto simp: lp_cut_fresh_def)
  have renamed: "lpc_return_scope_word [(m,k),(lp_cut_scope_swap m k n,l)]
      (lpp_probe_stack ?a (f=''1:once'') m n ?gs ?active ?saved)=tt"
    using lpp_probe_fresh_pair[OF em en fk el mn kl, where a="?a" and keep="f=''1:once''" and active="?active"] target by simp
  show ?thesis using renamed event
    by (auto simp only: lpp_probe_stack_eval)
qed


definition lpp_check_evaluation_probe where
  "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e =
    (lpp_probe_name f \<and>
     ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),active)#saved \<and>
     lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
     lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       (lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

theorem lpp_evaluation_probe_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?next = "lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs active saved"
  have name: "lpp_probe_name f"
    and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),active)#saved"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?next
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp only: lpp_check_evaluation_probe_def)
  obtain swaps where event: "event=None"
    and same: "tt=lpc_return_scope_word swaps (lpc_return_eval eta ?next)"
    using lpp_probe_checked_covers[OF name fm fn, where P=P and eta=eta and event=event and tt=tt and g=g and argv=argv and active=active] step
    by (auto simp only: shape)
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ?next)) u"
    using lpp_evaluation_link_sound[OF contract evaluation program link _ refl known free observed]
    by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

lemma lpp_evaluation_probe_domain:
  assumes checked: "lpp_check_evaluation_probe T fs fuel Q nds states contexts Fs nd F ss source_context f g argv m n gs active saved e"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
  using checked lpp_finite_probe_domain[of f g argv eta]
  by (auto simp: lpp_check_evaluation_probe_def lpc_return_eval_def)

ML \<open>
val checked = [@{thm lpp_evaluation_probe_sound}, @{thm lpp_evaluation_probe_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted opaque probe dependency" else ();
\<close>
end
