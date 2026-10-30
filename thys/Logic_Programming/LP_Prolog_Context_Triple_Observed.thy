theory LP_Prolog_Context_Triple_Observed
 imports LP_Prolog_Context_Observed_Control LP_Cut_SEG_Triple_Observed
begin

lemma lpp_triple_instance_stable:
  fixes a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes step: "lpp_answer_transition P B U ss event us"
    and invariant: "lpc_triple_instance_invariant a inp ss"
  shows "lpc_triple_instance_invariant a inp us"
proof -
  have stable: "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp (\<lambda>x. lp_isubst (eta x) sigma)"
    if witness: "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp eta"
    for eta :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
      and sigma :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  proof -
    obtain tau where match: "lp_iatom_subst a tau=lp_atom_eval inp eta" using witness by blast
    have "lp_iatom_subst a (\<lambda>x. lp_isubst (tau x) sigma)=
        lp_atom_eval inp (\<lambda>x. lp_isubst (eta x) sigma)"
      using arg_cong[OF match, of "\<lambda>b. lp_iatom_subst b sigma"]
      by (simp add: lp_iatom_subst_def lp_atom_eval_def lp_seg_isubst_comp
        lp_ieval_subst map_map o_def)
    then show ?thesis by blast
  qed
  show ?thesis unfolding lpc_triple_instance_invariant_def
    using lpp_answer_substitution_property[OF stable step
      invariant[unfolded lpc_triple_instance_invariant_def]] by blast
qed

lemma lpp_domain_triple_instance_stable:
  fixes a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes step: "lpp_domain_answers P B U D ss event us"
    and invariant: "lpc_triple_instance_invariant a inp ss"
  shows "lpc_triple_instance_invariant a inp us"
proof (cases "lpp_answer_transition P B U ss event us")
  case True
  show ?thesis by (rule lpp_triple_instance_stable[OF True invariant])
next
  case False
  show ?thesis using step False invariant by (simp add: lpp_domain_answers_def)
qed

lemma lpp_domain_source_answer_SN:
  fixes ss :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry *
    ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
  assumes sn: "SN_on (lpp_domain_source P B U D) {map fst ss}"
  shows "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {ss}"
proof -
  have all: "\<forall>us :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry *
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list. map fst us=s \<longrightarrow>
    SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {us}"
    if "SN_on (lpp_domain_source P B U D) {s}" for s
  proof (rule SN_on_induct[OF that singletonI], intro allI impI)
    fix s and us :: "(('f lp_cut_symbol,string) lp_iterm lp_cut_entry *
      ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list"
    assume ih: "\<And>t. (s,t)\<in>lpp_domain_source P B U D \<Longrightarrow>
      \<forall>vs :: (('f lp_cut_symbol,string) lp_iterm lp_cut_entry *
        ('v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm)) list. map fst vs=t \<longrightarrow> SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {vs}"
      and shape: "map fst us=s"
    show "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {us}"
    proof (rule step_reflects_SN_on)
      fix vs assume step: "(us,vs)\<in>lp_answer_steps (lpp_domain_answers P B U D)"
      obtain event where event: "lpp_domain_answers P B U D us event vs"
        using step by (auto simp: lp_answer_steps_def)
      have edge: "(s,map fst vs)\<in>lpp_domain_source P B U D"
        using lpp_domain_answers_erases[OF event] shape by simp
      show "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {vs}"
        using ih[OF edge] by simp
    qed
  qed
  show ?thesis using all[OF sn] by simp
qed


theorem lpp_context_control_source_SN:
  fixes SP :: "string lpp_success_clause list"
    and a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes checked: "lpp_check_context_control fuel P Q nds states contexts T typings returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of Q"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and represented: "lpp_context_module_rep SP nds states contexts ss control"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_source_context_holds SP (contexts!i) eta \<Longrightarrow>
      lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i)) \<Longrightarrow>
      SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        {map fst (lpc_return_eval eta (states!i))}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst ss}"
proof -
  have contract: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    ss ({} :: unit rel) () (\<lambda>_. ())"
  proof (rule lpp_context_observed_control_contract[where J="lpc_triple_instance_invariant a inp",
      OF checked ranked transfer program invariant _ _ lpc_triple_instance_scopes represented])
    show "\<And>xs ev ys. lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain xs ev ys \<Longrightarrow>
      lpc_triple_instance_invariant a inp xs \<Longrightarrow> lpc_triple_instance_invariant a inp ys"
      by (rule lpp_domain_triple_instance_stable)
  next
    show "\<And>xs ys. set xs \<subseteq> set ys \<Longrightarrow> lpc_triple_instance_invariant a inp ys \<Longrightarrow>
      lpc_triple_instance_invariant a inp xs" by (rule lpc_triple_instance_subset)
  next
    fix i eta assume index: "i<length nds" and boundary_node: "actions!i=None"
      and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
      and observed: "lpp_source_context_holds SP (contexts!i) eta"
      and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
    have sn: "SN_on (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))
      {lpc_return_eval eta (states!i)}"
      by (rule lpp_domain_source_answer_SN[OF boundary[OF index boundary_node known observed inv]])
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      (lpc_return_eval eta (states!i)) ({} :: unit rel) () (\<lambda>_. ())"
      using sn by (simp add: lp_answer_contract_def lp_answers_covered_def)
  next
    fix i eta rho tt
    show "((),())\<in>({}::unit rel)\<^sup>*" by (rule rtrancl_refl)
  qed
  show ?thesis by (rule lpp_domain_instrumentation_SN)
    (use contract in \<open>simp add: lp_answer_contract_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_domain_triple_instance_stable}, @{thm lpp_domain_source_answer_SN}, @{thm lpp_context_control_source_SN}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted Prolog triple instance dependency" else ();
\<close>
end
