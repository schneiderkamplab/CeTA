theory LP_Cut_Domain_Return_Source
  imports LP_Cut_Domain_Return_Attachment
begin

context cut_runtime_domain
begin

lemma precise_clause_nonempty_preserved:
  assumes step: "precise_answer_transition P ss event tt"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
  shows "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) tt"
  using step
proof (cases rule: precise_answer_transition.cases)
  case case_call then show ?thesis using valid by (auto simp: list_all_iff)
qed (use valid in \<open>auto intro: lpc_clause_nonempty_prune\<close>)

lemma precise_attach_barriers_preserved:
  assumes separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and step: "(lpc_attach rest ss,u)\<in>precise_source P"
  shows "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids u) = {}"
proof -
  have before: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (lpc_attach rest ss)) = {}"
    using separated by (simp add: lpc_attach_barriers)
  from step show ?thesis
  proof cases
    case admin
    have subset: "set (lpc_barrier_ids u) \<subseteq> set (lpc_barrier_ids (lpc_attach rest ss))"
      by (rule lpc_admin_barriers_subset[OF admin])
    show ?thesis using before subset by blast
  next
    case (case_call m f ts gs es)
    have fresh: "lp_cut_fresh m (lpc_attach rest ss)" using case_call by simp
    have m: "m\<notin>lpc_rest_scopes rest"
      by (rule lpc_attach_fresh_goals[OF fresh]) (use case_call in simp)
    show ?thesis using before case_call m by simp
  next
    case (meta m a gs es body)
    have fresh: "lp_cut_fresh m (lpc_attach rest ss)" using meta by simp
    have m: "m\<notin>lpc_rest_scopes rest"
      by (rule lpc_attach_fresh_goals[OF fresh]) (use meta in simp)
    show ?thesis using before meta m by simp
  qed (use before in auto)
qed

theorem precise_return_source_SN:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and contract: "precise_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>\<eta>. (t,ret \<eta>)\<in>R\<^sup>* \<Longrightarrow>
      SN_on (precise_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest)]}"
  shows "SN_on (precise_source P) {lpc_attach rest ss}"
proof -
  let ?E = "lpc_rest_scopes rest"
  have prefix_sn: "SN_on (precise_answer_steps P) {ss}"
    using contract precise_answer_instrumentation_SN
    unfolding precise_return_contract_def by blast
  have all: "(ss,us)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<longrightarrow>
    ?E\<inter>set (lpc_barrier_ids (map fst us))={} \<longrightarrow>
    SN_on (precise_source P) {lpc_attach rest us}"
    if sn: "SN_on (precise_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>precise_answer_steps P \<Longrightarrow>
      (ss,vs)\<in>(precise_answer_steps P)\<^sup>* \<longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs \<longrightarrow>
      ?E\<inter>set (lpc_barrier_ids (map fst vs))={} \<longrightarrow>
      SN_on (precise_source P) {lpc_attach rest vs}"
      and path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
      and well: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us"
      and disjoint: "?E\<inter>set (lpc_barrier_ids (map fst us))={}"
    have child: "SN_on (precise_source P) {lpc_attach rest vs}"
      if event: "precise_answer_transition P us ev vs"
        and sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}" for ev vs
    proof -
      have step: "(us,vs)\<in>precise_answer_steps P"
        using event by (auto simp: precise_answer_steps_def)
      have reached: "(ss,vs)\<in>(precise_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path step])
      have well_child: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
        by (rule precise_clause_nonempty_preserved[OF event well])
      show ?thesis using ih[OF step] reached well_child sep by blast
    qed
    show "SN_on (precise_source P) {lpc_attach rest us}"
    proof (cases "lpc_prefix_active us")
      case True
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix u assume step: "(lpc_attach rest us,u)\<in>precise_source P"
        obtain vs where event: "precise_answer_transition P us None vs"
          and shape: "u=lpc_attach rest vs"
          using precise_attach_active_reflect[OF True step] by blast
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using precise_attach_barriers_preserved[OF disjoint step]
          by (simp add: shape lpc_attach_barriers)
        show "SN_on (precise_source P) {u}"
          using child[OF event sep] by (simp add: shape)
      qed
    next
      case False
      show ?thesis
      proof (cases us)
        case Nil
        show ?thesis unfolding Nil by (rule step_reflects_SN_on)
          (auto elim: precise_source.cases)
      next
        case (Cons frame vs)
        obtain e \<eta> where frame: "frame=(e,\<eta>)" by (cases frame) auto
        have e: "e=LPCGoals []" using False well Cons frame by (cases e) auto
        have event: "precise_answer_transition P us (Some \<eta>) vs"
          by (simp add: Cons frame e precise_answer_transition.success)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using disjoint by (simp add: Cons frame e)
        have tail_sn: "SN_on (precise_source P) {lpc_attach rest vs}"
          by (rule child[OF event sep])
        let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest"
        have first: "SN_on (precise_source P) {[LPCGoals ?gs]}"
          by (rule precise_return_contract_success[OF contract path event continuation])
        have owns: "lpc_owned_stack ?E [LPCGoals ?gs]"
          using lpc_owned_external_goals[of rest ?E "[]"]
          by (simp add: lpc_owned_goals_map)
        have separated_tail: "?E\<inter>set (lpc_barrier_ids (lpc_attach rest vs))={}"
          using sep by (simp add: lpc_attach_barriers)
        have attached: "SN_on (precise_source P) {[LPCGoals ?gs]@lpc_attach rest vs}"
          by (rule precise_owned_append_SN[OF program owns separated_tail first tail_sn])
        show ?thesis using attached by (simp add: Cons frame e)
      qed
    qed
  qed
  show ?thesis using all[OF prefix_sn] valid separated by simp
qed

corollary precise_cut_prefix_return_contract_SN:
  fixes P :: "('f,string) lp_cut_program"
    and prefix :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
  assumes program: "lp_cut_source_program P"
    and contract: "precise_return_contract P [(LPCGoals prefix,\<eta>)] R t ret"
    and continuation: "\<And>\<rho>. (t,ret \<rho>)\<in>R\<^sup>* \<Longrightarrow>
      SN_on (precise_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x \<rho>)) rest)]}"
  shows "SN_on (precise_source P)
    {[LPCGoals (prefix @ map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest)]}"
  using precise_return_source_SN[OF program contract, where rest=rest] continuation by simp

end
end
