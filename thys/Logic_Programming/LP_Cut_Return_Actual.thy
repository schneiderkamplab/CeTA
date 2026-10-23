theory LP_Cut_Return_Actual
  imports LP_Cut_Return_Attached_Answers
begin

definition lpc_actual_return where
  "lpc_actual_return P ss eta =
    (\<exists>us tail. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<and> lpc_answer_transition P us (Some eta) tail)"

lemma lpc_actual_return_residual:
  "lpc_return_contract P ss R t ret \<Longrightarrow> lpc_actual_return P ss eta \<Longrightarrow> (t,ret eta)\<in>R\<^sup>*"
  by (auto simp: lpc_return_contract_def lpc_actual_return_def)

theorem lpc_return_source_SN_actual:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and contract: "lpc_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and continuation: "\<And>\<eta>. lpc_actual_return P ss \<eta> \<Longrightarrow>
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
          by (rule continuation) (use path event in \<open>auto simp: lpc_actual_return_def\<close>)
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

theorem lpc_attach_answers_covered_actual:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and contract: "lpc_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation_sn: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      SN_on (lp_cut_mgu_source P) {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
    and continuation_answers: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      lpc_answers_covered P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] C"
  shows "lpc_answers_covered P (lpc_attach_answers rest ss) C"
proof -
  let ?E = "lpc_rest_scopes rest"
  have sn: "SN_on (lpc_answer_steps P) {ss}"
    using contract lpc_answer_instrumentation_SN unfolding lpc_return_contract_def by blast
  have all: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<longrightarrow>
    ?E\<inter>set (lpc_barrier_ids (map fst us))={} \<longrightarrow>
    lpc_answers_covered P (lpc_attach_answers rest us) C"
    if finite: "SN_on (lpc_answer_steps P) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>lpc_answer_steps P \<Longrightarrow>
      (ss,vs)\<in>(lpc_answer_steps P)\<^sup>* \<longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs \<longrightarrow>
      ?E\<inter>set (lpc_barrier_ids (map fst vs))={} \<longrightarrow>
      lpc_answers_covered P (lpc_attach_answers rest vs) C"
      and path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
      and well: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us"
      and disjoint: "?E\<inter>set (lpc_barrier_ids (map fst us))={}"
    have child: "lpc_answers_covered P (lpc_attach_answers rest vs) C"
      if event: "lpc_answer_transition P us ev vs"
        and sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}" for ev vs
    proof -
      have edge: "(us,vs)\<in>lpc_answer_steps P"
        using event by (auto simp: lpc_answer_steps_def)
      have reached: "(ss,vs)\<in>(lpc_answer_steps P)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path edge])
      have valid_child: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
        by (rule lpc_clause_nonempty_preserved[OF event well])
      show ?thesis using ih[OF edge] reached valid_child sep by blast
    qed
    show "lpc_answers_covered P (lpc_attach_answers rest us) C"
    proof (cases "lpc_prefix_active us")
      case True
      show ?thesis
      proof (rule lpc_answers_covered_intro)
        fix event u assume step: "lpc_answer_transition P (lpc_attach_answers rest us) event u"
        obtain vs where silent: "event=None" and event: "lpc_answer_transition P us None vs"
          and shape: "u=lpc_attach_answers rest vs"
          using lpc_attach_answers_active_reflect[OF True step] by blast
        have source: "(lpc_attach rest us,lpc_attach rest vs)\<in>lp_cut_mgu_source P"
          using lpc_answer_transition_erases[OF step] by (simp add: shape lpc_attach_answers_erases)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using lpc_attach_barriers_preserved[OF disjoint source] by (simp add: lpc_attach_barriers)
        show "(\<forall>rho. event=Some rho \<longrightarrow> C rho) \<and> lpc_answers_covered P u C"
          using child[OF event sep] by (simp add: shape silent)
      qed
    next
      case False
      show ?thesis
      proof (cases us)
        case Nil
        show ?thesis unfolding Nil lpc_attach_answers_def
          by (rule lpc_answers_covered_intro) (auto elim: lpc_answer_transition.cases)
      next
        case (Cons frame vs)
        obtain e eta where frame: "frame=(e,eta)" by (cases frame) auto
        have e: "e=LPCGoals []" using False well Cons frame by (cases e) auto
        have event: "lpc_answer_transition P us (Some eta) vs"
          by (simp add: Cons frame e lpc_answer_transition.success)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs))={}"
          using disjoint by (simp add: Cons frame e)
        have tail: "lpc_answers_covered P (lpc_attach_answers rest vs) C"
          by (rule child[OF event sep])
        let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest"
        have actual: "lpc_actual_return P ss eta" using path event by (auto simp: lpc_actual_return_def)
        have reached: "(t,ret eta)\<in>R\<^sup>*"
          using contract path event unfolding lpc_return_contract_def by blast
        have first_sn: "SN_on (lpc_answer_steps P) {[(LPCGoals ?gs,eta)]}"
          using continuation_sn[OF actual] by (simp add: lpc_answer_instrumentation_SN)
        have first: "lpc_answers_covered P [(LPCGoals ?gs,eta)] C"
          by (rule continuation_answers[OF actual])
        have owns: "lpc_owned_stack ?E (map fst [(LPCGoals ?gs,eta)])"
          using lpc_owned_external_goals[of rest ?E "[]"] by (simp add: lpc_owned_goals_map)
        have separated_tail: "?E\<inter>set (lpc_barrier_ids (map fst (lpc_attach_answers rest vs)))={}"
          using sep by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
        have joined: "lpc_answers_covered P ([(LPCGoals ?gs,eta)] @ lpc_attach_answers rest vs) C"
          by (rule lpc_owned_answers_append[OF program owns separated_tail first_sn first tail])
        show ?thesis using joined by (simp add: Cons frame e lpc_attach_answers_def)
      qed
    qed
  qed
  show ?thesis using all[OF sn] valid separated by simp
qed


theorem lpc_return_contract_compose_actual:
  fixes P :: "('f,string) lp_cut_program"
  assumes program: "lp_cut_source_program P"
    and prefix: "lpc_return_contract P ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
    and continuation: "\<And>eta. lpc_actual_return P ss eta \<Longrightarrow>
      lpc_return_contract P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "lpc_return_contract P (lpc_attach_answers rest ss) R t final"
proof -
  have continuation_sn: "SN_on (lp_cut_mgu_source P)
      {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)]}"
    if "lpc_actual_return P ss eta" for eta
    using continuation[OF that] by (simp add: lpc_return_contract_def)
  have source: "SN_on (lp_cut_mgu_source P) {lpc_attach rest ss}"
    by (rule lpc_return_source_SN_actual[OF program prefix valid separated continuation_sn])
  have answers: "lpc_answers_covered P (lpc_attach_answers rest ss) (\<lambda>rho. (t,final rho)\<in>R\<^sup>*)"
  proof (rule lpc_attach_answers_covered_actual[OF program prefix valid separated continuation_sn])
    fix eta assume actual: "lpc_actual_return P ss eta"
    have reached: "(t,ret eta)\<in>R\<^sup>*" by (rule lpc_actual_return_residual[OF prefix actual])
    show "lpc_answers_covered P [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)]
      (\<lambda>rho. (t,final rho)\<in>R\<^sup>*)"
    proof (unfold lpc_answers_covered_def, intro allI impI)
      fix us rho vs
      assume path: "([(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)],us)
          \<in>(lpc_answer_steps P)\<^sup>*"
        and event: "lpc_answer_transition P us (Some rho) vs"
      have tail: "(ret eta,final rho)\<in>R\<^sup>*"
        using continuation[OF actual] path event unfolding lpc_return_contract_def by blast
      show "(t,final rho)\<in>R\<^sup>*" by (rule rtrancl_trans[OF reached tail])
    qed
  qed
  show ?thesis using source answers
    by (auto simp: lpc_return_contract_def lpc_answers_covered_def lpc_attach_answers_erases)
qed

end

