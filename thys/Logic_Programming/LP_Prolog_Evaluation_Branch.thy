theory LP_Prolog_Evaluation_Branch
  imports LP_Prolog_Finite_Branch LP_Prolog_Evaluation_Allocate
begin

lemma lpp_branch_stack_eval:
  "lpc_return_eval eta (lpp_branch_stack cs ys zs m n gs active saved) =
    lpp_branch_stack (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) cs) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) ys) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) zs) m n
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
      (lpc_return_env active eta) (lpc_return_eval eta saved)"
  by (simp add: lpc_return_eval_def lpp_branch_stack_def map_append)

lemma lpp_branch_checked_covers:
  assumes lower: "lpp_branch_lower_term c=Some cs" "lpp_branch_lower_term y=Some ys" "lpp_branch_lower_term z=Some zs"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [Fun (LPCUser ''2:->'') [c,y],z])#gs),active)#saved)) event tt"
  shows "event=None \<and> (\<exists>swaps. tt=lpc_return_scope_word swaps
    (lpc_return_eval eta (lpp_branch_stack cs ys zs m n gs active saved)))"
proof -
  let ?gs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  let ?saved = "lpc_return_eval eta saved"
  let ?cs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) cs"
  let ?ys = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) ys"
  let ?zs = "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) zs"
  let ?active = "lpc_return_env active eta"
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:;'') [LPIFun (LPCUser ''2:->'') [lp_ieval c eta,lp_ieval y eta],lp_ieval z eta])#?gs),?active)#?saved) event tt"
    using step by (simp add: lpc_return_eval_def)
  obtain k l where event: "event=None"
    and fk: "lp_cut_fresh k (LPCGoals ?gs#map fst ?saved)"
    and fl: "lp_cut_fresh l (LPCBarrier k#LPCGoals ?gs#map fst ?saved)"
    and target: "tt=lpp_branch_stack ?cs ?ys ?zs k l ?gs ?active ?saved"
    using lpp_finite_branch_step[OF lpp_branch_lower_term_sound[OF lower(1)] lpp_branch_lower_term_sound[OF lower(2)] lpp_branch_lower_term_sound[OF lower(3)] actual] by auto
  have em: "lp_cut_fresh m (LPCGoals ?gs#map fst ?saved)"
    using fm lp_cut_fresh_state_map[of m "\<lambda>t. lp_ieval t eta" "LPCGoals gs#map fst saved"]
    by (simp add: lpc_return_eval_erases lp_cut_state_map_def)
  have en: "lp_cut_fresh n (LPCGoals ?gs#map fst ?saved)"
    using fn lp_cut_fresh_state_map[of n "\<lambda>t. lp_ieval t eta" "LPCGoals gs#map fst saved"]
    by (simp add: lpc_return_eval_erases lp_cut_state_map_def lp_cut_fresh_def)
  have el: "lp_cut_fresh l (LPCGoals ?gs#map fst ?saved)"
    and kl: "k\<noteq>l" using fl by (auto simp: lp_cut_fresh_def)
  have mn: "m\<noteq>n" using fn by (auto simp: lp_cut_fresh_def)
  have plain: "list_all lpp_plain_goal (?cs@?ys@?zs)"
    using lpp_branch_lower_plain[OF lpp_branch_lower_term_sound[where eta=eta, OF lower(1)]]
      lpp_branch_lower_plain[OF lpp_branch_lower_term_sound[where eta=eta, OF lower(2)]]
      lpp_branch_lower_plain[OF lpp_branch_lower_term_sound[where eta=eta, OF lower(3)]] by simp
  have renamed: "lpc_return_scope_word [(m,k),(lp_cut_scope_swap m k n,l)]
      (lpp_branch_stack ?cs ?ys ?zs m n ?gs ?active ?saved)=tt"
    using lpp_branch_fresh_pair[OF plain em en fk el mn kl, where active="?active"] target by simp
  show ?thesis using renamed event
    by (auto simp only: lpp_branch_stack_eval)
qed


definition lpp_check_evaluation_branch where
  "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e =
    (lpp_branch_lower_term c=Some cs \<and> lpp_branch_lower_term y=Some ys \<and> lpp_branch_lower_term z=Some zs \<and>
     ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [Fun (LPCUser ''2:->'') [c,y],z])#gs),active)#saved \<and>
     lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
     lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       (lpp_branch_stack cs ys zs m n gs active saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F source_context e)"

theorem lpp_evaluation_branch_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_finite_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u)"
proof -
  let ?next = "lpp_branch_stack cs ys zs m n gs active saved"
  have lower: "lpp_branch_lower_term c=Some cs" "lpp_branch_lower_term y=Some ys" "lpp_branch_lower_term z=Some zs"
    and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:;'') [Fun (LPCUser ''2:->'') [c,y],z])#gs),active)#saved"
    and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
    and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?next
      (lpcn_ground nd) (lpcn_guards nd) [] F source_context e"
    using checked by (auto simp only: lpp_check_evaluation_branch_def)
  obtain swaps where event: "event=None"
    and same: "tt=lpc_return_scope_word swaps (lpc_return_eval eta ?next)"
    using lpp_branch_checked_covers[OF lower fm fn, where P=P and eta=eta and event=event and tt=tt and active=active] step
    by (auto simp only: shape)
  have child: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps (lpc_return_eval eta ?next)) u"
    using lpp_evaluation_link_sound[OF contract evaluation program link _ refl known free observed]
    by (simp add: lp_equations_def)
  show ?thesis using lpc_return_scoped_successor[OF same child] event by blast
qed

lemma lpp_evaluation_branch_domain:
  assumes checked: "lpp_check_evaluation_branch T fs fuel Q nds states contexts Fs nd F ss source_context c y z cs ys zs m n gs active saved e"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_finite_source_domain (map fst (lpc_return_eval eta ss))"
  using checked lpp_finite_branch_domain[of c cs y ys z zs eta]
  by (auto simp: lpp_check_evaluation_branch_def lpc_return_eval_def)

ML \<open>
val checked = [@{thm lpp_evaluation_branch_sound}, @{thm lpp_evaluation_branch_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted opaque probe dependency" else ();
\<close>
end
