theory LP_Scoped_Answer_Invariant_Composition
 imports LP_Scoped_Answer_Composition
begin

text \<open>The invariant follows the attached execution, not arbitrary standalone
prefix answers. It is preserved on actual attached steps and when a completed
prefix frame is removed. This retains continuation observations that need not be
preserved by the larger standalone-prefix answer relation.\<close>

theorem lp_scoped_answer_contract_compose_actual_invariant:
  assumes prefix: "lp_answer_contract T ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and initial: "I ss"
    and invariant_step: "\<And>us ev vs. I us \<Longrightarrow>
      (ss,us)\<in>(lp_answer_steps T)\<^sup>* \<Longrightarrow> lpc_prefix_active us \<Longrightarrow>
      T (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow> I vs"
    and invariant_tail: "\<And>eta vs. I ((LPCGoals [],eta)#vs) \<Longrightarrow> I vs"
    and continuation: "\<And>eta vs. lp_actual_answer T ss eta \<Longrightarrow>
      I ((LPCGoals [],eta)#vs) \<Longrightarrow> lp_answer_contract T
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
    and valid_step: "\<And>us ev vs. T us ev vs \<Longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<Longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
    and reflect: "\<And>us ev result. lpc_prefix_active us \<Longrightarrow>
      T (lpc_attach_answers rest us) ev result \<Longrightarrow>
      ev = None \<and> (\<exists>vs. T us None vs \<and> result = lpc_attach_answers rest vs)"
    and separate_step: "\<And>us ev vs. lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {} \<Longrightarrow>
      T (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
      lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
    and empty: "\<And>ev vs. \<not>T [] ev vs"
    and success: "\<And>eta vs. T ((LPCGoals [],eta)#vs) (Some eta) vs"
    and append: "\<And>us vs. lpc_owned_stack (lpc_rest_scopes rest) (map fst us) \<Longrightarrow>
      lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {} \<Longrightarrow>
      lp_answer_contract T us R t final \<Longrightarrow>
      lp_answer_contract T vs R t final \<Longrightarrow>
      lp_answer_contract T (us@vs) R t final"
  shows "lp_answer_contract T (lpc_attach_answers rest ss) R t final"
proof -
  let ?T = "T"
  let ?E = "lpc_rest_scopes rest"
  have sn: "SN_on (lp_answer_steps ?T) {ss}" using prefix by (simp add: lp_answer_contract_def)
  have all: "(ss,us)\<in>(lp_answer_steps ?T)\<^sup>* \<longrightarrow> I us \<longrightarrow>
      list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<longrightarrow>
      ?E\<inter>set (lpc_barrier_ids (map fst us)) = {} \<longrightarrow>
      lp_answer_contract ?T (lpc_attach_answers rest us) R t final"
    if finite: "SN_on (lp_answer_steps ?T) {us}" for us
  proof (rule SN_on_induct[OF finite singletonI], intro impI)
    fix us
    assume ih: "\<And>vs. (us,vs)\<in>lp_answer_steps ?T \<Longrightarrow>
        (ss,vs)\<in>(lp_answer_steps ?T)\<^sup>* \<longrightarrow> I vs \<longrightarrow>
        list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs \<longrightarrow>
        ?E\<inter>set (lpc_barrier_ids (map fst vs)) = {} \<longrightarrow>
        lp_answer_contract ?T (lpc_attach_answers rest vs) R t final"
      and path: "(ss,us)\<in>(lp_answer_steps ?T)\<^sup>*"
      and invariant: "I us"
      and well: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us"
      and disjoint: "?E\<inter>set (lpc_barrier_ids (map fst us)) = {}"
    have child: "lp_answer_contract ?T (lpc_attach_answers rest vs) R t final"
      if event: "?T us ev vs" and sep: "?E\<inter>set (lpc_barrier_ids (map fst vs)) = {}"
      and child_invariant: "I vs" for ev vs
    proof -
      have edge: "(us,vs)\<in>lp_answer_steps ?T" using event by (auto simp: lp_answer_steps_def)
      have reached: "(ss,vs)\<in>(lp_answer_steps ?T)\<^sup>*"
        by (rule rtrancl_into_rtrancl[OF path edge])
      have valid_child: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
        by (rule valid_step[OF event well])
      show ?thesis using ih[OF edge] reached valid_child sep child_invariant by blast
    qed
    show "lp_answer_contract ?T (lpc_attach_answers rest us) R t final"
    proof (cases "lpc_prefix_active us")
      case True
      show ?thesis
      proof (rule lp_answer_contract_intro)
        fix event u assume step: "?T (lpc_attach_answers rest us) event u"
        obtain vs where silent: "event = None" and local: "?T us None vs"
          and shape: "u = lpc_attach_answers rest vs"
          using reflect[OF True step] by blast
        have sep: "?E \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
          by (rule separate_step[OF disjoint]) (use step shape in simp)
        have child_invariant: "I vs"
          by (rule invariant_step[OF invariant path True]) (use step shape in simp)
        show "(\<forall>rho. event = Some rho \<longrightarrow> (t,final rho)\<in>R\<^sup>*) \<and>
          lp_answer_contract ?T u R t final" using child[OF local sep child_invariant] by (simp add: shape silent)
      qed
    next
      case False
      show ?thesis
      proof (cases us)
        case Nil
        show ?thesis unfolding Nil lpc_attach_answers_def
          by (rule lp_answer_contract_intro)
            (use empty in auto)
      next
        case (Cons frame vs)
        obtain e eta where frame: "frame = (e,eta)" by (cases frame) auto
        have e: "e = LPCGoals []" using False well Cons frame by (cases e) auto
        have event: "?T us (Some eta) vs"
          unfolding Cons frame e by (rule success)
        have sep: "?E\<inter>set (lpc_barrier_ids (map fst vs)) = {}"
          using disjoint by (simp add: Cons frame e)
        have tail_invariant: "I vs"
          by (rule invariant_tail[of eta]) (use invariant in \<open>simp add: Cons frame e\<close>)
        have tail: "lp_answer_contract ?T (lpc_attach_answers rest vs) R t final"
          by (rule child[OF event sep tail_invariant])
        have reached: "(t,ret eta)\<in>R\<^sup>*"
          using prefix path event by (auto simp: lp_answer_contract_def lp_answers_covered_def)
        let ?gs = "map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest"
        have actual: "lp_actual_answer ?T ss eta"
          using path event by (auto simp: lp_actual_answer_def)
        have continued: "lp_answer_contract ?T [(LPCGoals ?gs,eta)] R (ret eta) final"
          by (rule continuation[OF actual]) (use invariant in \<open>simp add: Cons frame e\<close>)
        have first: "lp_answer_contract ?T [(LPCGoals ?gs,eta)] R t final"
          by (rule lp_answer_contract_start[OF reached continued])
        have owns: "lpc_owned_stack ?E (map fst [(LPCGoals ?gs,eta)])"
          using lpc_owned_external_goals[of rest ?E "[]"] by (simp add: lpc_owned_goals_map)
        have separated_tail: "?E\<inter>set (lpc_barrier_ids (map fst (lpc_attach_answers rest vs))) = {}"
          using sep by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
        have joined: "lp_answer_contract ?T ([(LPCGoals ?gs,eta)]@lpc_attach_answers rest vs) R t final"
          by (rule append[OF owns separated_tail first tail])
        show ?thesis using joined by (simp add: Cons frame e lpc_attach_answers_def)
      qed
    qed
  qed
  show ?thesis using all[OF sn] valid separated initial by simp
qed


lemmas lp_scoped_answer_contract_compose_unrestricted =
 lp_scoped_answer_contract_compose_actual_invariant[where I="\<lambda>_. True", simplified]

ML \<open>
val checked = @{thms lp_scoped_answer_contract_compose_actual_invariant lp_scoped_answer_contract_compose_unrestricted};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted invariant answer composition" else ();
\<close>
end
