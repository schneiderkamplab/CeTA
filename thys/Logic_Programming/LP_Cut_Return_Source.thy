theory LP_Cut_Return_Source
  imports LP_Cut_Scope_Ownership
begin

abbreviation lpc_rest_scopes where
  "lpc_rest_scopes rest \<equiv> \<Union>(lp_cut_goal_scopes ` set rest)"

fun lpc_clause_nonempty where
  "lpc_clause_nonempty (LPCClause gs c m) = (gs\<noteq>[])"
| "lpc_clause_nonempty e = True"

lemma lpc_clause_nonempty_prune:
  "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) (lpc_answer_prune m ss)"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits)

lemma lpc_clause_nonempty_preserved:
  assumes step: "lpc_answer_transition P ss event tt"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
  shows "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) tt"
  using step
proof (cases rule: lpc_answer_transition.cases)
  case case_call then show ?thesis using valid by (auto simp: list_all_iff)
qed (use valid in \<open>auto intro: lpc_clause_nonempty_prune\<close>)

lemma lpc_attach_barriers:
  "lpc_barrier_ids (lpc_attach rest ss) = lpc_barrier_ids (map fst ss)"
proof (induct ss)
  case Nil then show ?case by simp
next
  case (Cons frame ss)
  then show ?case by (cases frame; cases "fst frame") auto
qed

lemma lpc_attach_fresh_goals:
  assumes fresh: "lp_cut_fresh m (lpc_attach rest ss)"
    and goals: "lpc_attach rest ss = LPCGoals gs#es"
  shows "m\<notin>lpc_rest_scopes rest"
proof -
  obtain e \<eta> tail where ss: "ss=(e,\<eta>)#tail"
    using goals by (cases ss; auto split: prod.splits)
  obtain prefix where e: "e=LPCGoals prefix" using goals ss by (cases e) auto
  show ?thesis using fresh by (auto simp: ss e lp_cut_fresh_def)
qed

lemma lpc_admin_barriers_subset:
  "lp_cut_admin ss=Some tt \<Longrightarrow>
    set (lpc_barrier_ids tt) \<subseteq> set (lpc_barrier_ids ss)"
proof (induct ss rule: lp_cut_admin.induct)
  case (5 g gs es)
  then show ?case by (cases g)
    (auto simp: lpc_barrier_ids_prune dest: set_dropWhileD)
qed auto

lemma lpc_attach_barriers_preserved:
  assumes separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and step: "(lpc_attach rest ss,u)\<in>lp_cut_mgu_source P"
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

lemma lpc_owned_external_goals:
  assumes "lpc_rest_scopes rest \<subseteq> E"
  shows "lpc_owned_goals E B rest"
  using assms
proof (induct rest arbitrary: B)
  case Nil then show ?case by simp
next
  case (Cons g rest) then show ?case by (cases g) auto
qed

theorem lpc_return_source_SN:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and contract: "lpc_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>\<eta>. (t,ret \<eta>)\<in>R\<^sup>* \<Longrightarrow>
      SN_on (lp_cut_mgu_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest)]}"
  shows "SN_on (lp_cut_mgu_source P) {lpc_attach rest ss}"
proof -
  let ?E = "lpc_rest_scopes rest"
  have prefix_sn: "SN_on (lpc_answer_steps P) {ss}"
    using contract lpc_answer_instrumentation_SN
    unfolding lpc_return_contract_def by blast
  have all: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<longrightarrow>
    ?E\<inter>set (lpc_barrier_ids (map fst us))={} \<longrightarrow>
    SN_on (lp_cut_mgu_source P) {lpc_attach rest us}"
    if sn: "SN_on (lpc_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>lpc_answer_steps P \<Longrightarrow>
      (ss,vs)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs \<longrightarrow>
      ?E\<inter>set (lpc_barrier_ids (map fst vs))={} \<longrightarrow>
      SN_on (lp_cut_mgu_source P) {lpc_attach rest vs}"
      and path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
      and well: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us"
      and disjoint: "?E\<inter>set (lpc_barrier_ids (map fst us))={}"
    have child: "SN_on (lp_cut_mgu_source P) {lpc_attach rest vs}"
      if event: "lpc_answer_transition P us ev vs"
        and sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}" for ev vs
    proof -
      have step: "(us,vs)\<in>lpc_answer_steps P"
        using event by (auto simp: lpc_answer_steps_def)
      have reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path step])
      have well_child: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
        by (rule lpc_clause_nonempty_preserved[OF event well])
      show ?thesis using ih[OF step] reached well_child sep by blast
    qed
    show "SN_on (lp_cut_mgu_source P) {lpc_attach rest us}"
    proof (cases "lpc_prefix_active us")
      case True
      show ?thesis
      proof (rule step_reflects_SN_on)
        fix u assume step: "(lpc_attach rest us,u)\<in>lp_cut_mgu_source P"
        obtain vs where event: "lpc_answer_transition P us None vs"
          and shape: "u=lpc_attach rest vs"
          using lpc_attach_active_reflect[OF True step] by blast
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using lpc_attach_barriers_preserved[OF disjoint step]
          by (simp add: shape lpc_attach_barriers)
        show "SN_on (lp_cut_mgu_source P) {u}"
          using child[OF event sep] by (simp add: shape)
      qed
    next
      case False
      show ?thesis
      proof (cases us)
        case Nil
        show ?thesis unfolding Nil by (rule step_reflects_SN_on)
          (auto elim: lp_cut_mgu_source.cases)
      next
        case (Cons frame vs)
        obtain e \<eta> where frame: "frame=(e,\<eta>)" by (cases frame) auto
        have e: "e=LPCGoals []" using False well Cons frame by (cases e) auto
        have event: "lpc_answer_transition P us (Some \<eta>) vs"
          by (simp add: Cons frame e lpc_answer_transition.success)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using disjoint by (simp add: Cons frame e)
        have tail_sn: "SN_on (lp_cut_mgu_source P) {lpc_attach rest vs}"
          by (rule child[OF event sep])
        let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest"
        have first: "SN_on (lp_cut_mgu_source P) {[LPCGoals ?gs]}"
          by (rule lpc_return_contract_success[OF contract path event continuation])
        have owns: "lpc_owned_stack ?E [LPCGoals ?gs]"
          using lpc_owned_external_goals[of rest ?E "[]"]
          by (simp add: lpc_owned_goals_map)
        have separated_tail: "?E\<inter>set (lpc_barrier_ids (lpc_attach rest vs))={}"
          using sep by (simp add: lpc_attach_barriers)
        have attached: "SN_on (lp_cut_mgu_source P) {[LPCGoals ?gs]@lpc_attach rest vs}"
          by (rule lpc_owned_append_SN[OF program owns separated_tail first tail_sn])
        show ?thesis using attached by (simp add: Cons frame e)
      qed
    qed
  qed
  show ?thesis using all[OF prefix_sn] valid separated by simp
qed

corollary lpc_cut_prefix_return_contract_SN:
  fixes P :: "('f,string) lp_cut_program"
    and prefix :: "('f lp_cut_symbol,string) lp_iterm lp_cut_goal list"
  assumes program: "lp_cut_source_program P"
    and contract: "lpc_return_contract P [(LPCGoals prefix,\<eta>)] R t ret"
    and continuation: "\<And>\<rho>. (t,ret \<rho>)\<in>R\<^sup>* \<Longrightarrow>
      SN_on (lp_cut_mgu_source P)
        {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x \<rho>)) rest)]}"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals (prefix @ map (lp_cut_map (\<lambda>x. lp_ieval x \<eta>)) rest)]}"
  using lpc_return_source_SN[OF program contract, where rest=rest] continuation by simp

end
