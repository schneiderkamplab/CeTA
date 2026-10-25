theory LP_Cut_SEG_Triple_Observed
  imports LP_Cut_SEG_Triple_Prefix LP_Cut_SEG_Observed_Control
begin

definition lpc_triple_instance_invariant where
  "lpc_triple_instance_invariant a inp ss =
    list_all (\<lambda>e. \<exists>sigma. lp_iatom_subst a sigma=lp_atom_eval inp (snd e)) ss"

lemma lpc_triple_instance_stable:
  fixes a :: "('f lp_cut_symbol,string) lp_iatom"
    and inp :: "('f lp_cut_symbol,nat) lp_atom"
  assumes step: "lpc_answer_transition P ss event us"
    and invariant: "lpc_triple_instance_invariant a inp ss"
  shows "lpc_triple_instance_invariant a inp us"
proof -
  have stable: "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp (\<lambda>x. lp_isubst (eta x) sigma)"
    if witness: "\<exists>tau. lp_iatom_subst a tau=lp_atom_eval inp eta"
    for eta :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
      and sigma :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
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
    using lpc_answer_substitution_property[OF stable step
      invariant[unfolded lpc_triple_instance_invariant_def]] by blast
qed

lemma lpc_triple_instance_subset:
  "set xs \<subseteq> set ys \<Longrightarrow> lpc_triple_instance_invariant a inp ys \<Longrightarrow>
    lpc_triple_instance_invariant a inp xs"
  by (auto simp: lpc_triple_instance_invariant_def list_all_iff)

lemma lpc_triple_instance_scopes:
  "lpc_triple_instance_invariant a inp (lpc_return_scope_word swaps ss) =
    lpc_triple_instance_invariant a inp ss"
proof (induct swaps arbitrary: ss)
  case Nil show ?case by simp
next
  case (Cons swap swaps)
  obtain i j where swap: "swap=(i,j)" by (cases swap) auto
  show ?case by (simp only: swap lpc_return_scope_word.simps Cons.hyps)
    (simp add: lpc_triple_instance_invariant_def list_all_iff)
qed

definition lpc_triple_observation_atom where
  "lpc_triple_observation_atom observed a =
    (fst a,map (lpc_seg_compose_observation observed) (snd a))"

lemma lpc_triple_observation_atom_eval:
  "lp_atom_eval a (lpc_return_env observed eta) =
    lp_atom_eval (lpc_triple_observation_atom observed a) eta"
proof -
  have env: "(\<lambda>n. lp_ieval (if n<length observed then observed!n else Fun LPCTruth []) eta)
      =lpc_return_env observed eta"
    by (rule ext) (simp add: lpc_return_env_def)
  show ?thesis by (simp add: lpc_triple_observation_atom_def lp_atom_eval_def
    lpc_seg_compose_observation_def lp_ieval_finite_subst env map_map o_def)
qed

definition lpc_triple_check_emit where
  "lpc_triple_check_emit Q out ss c bindings =
    (case ss of (LPCGoals [],observed)#rest \<Rightarrow>
      lpc_triple_check_model_clause Q [] (lpc_triple_observation_atom observed out) c bindings
    | _ \<Rightarrow> True)"

lemma lpc_triple_checked_emit:
  assumes checked: "lpc_triple_check_emit Q out ss c bindings"
    and event: "lpc_answer_transition P (lpc_return_eval eta ss) (Some rho) tt"
  shows "lp_answer_model Q (lp_atom_eval out rho)"
proof -
  have runtime: "lpc_return_eval eta ss=(LPCGoals [],rho)#tt"
    using event by (cases rule: lpc_answer_transition.cases) auto
  obtain e observed rest where ss: "ss=(e,observed)#rest"
    using runtime by (cases ss) (auto simp: lpc_return_eval_def)
  have head: "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e=LPCGoals []"
    and rho: "rho=lpc_return_env observed eta"
    using runtime by (simp_all add: ss lpc_return_eval_def)
  have e: "e=LPCGoals []" using head by (cases e) auto
  have receipt: "lpc_triple_check_model_clause Q []
    (lpc_triple_observation_atom observed out) c bindings"
    using checked by (simp add: lpc_triple_check_emit_def ss e)
  show ?thesis unfolding rho lpc_triple_observation_atom_eval
    by (rule lpc_triple_checked_model_clause[OF receipt]) simp
qed

theorem lpc_triple_observed_control:
  fixes P :: "('f,string) lp_cut_program"
    and a :: "('f lp_cut_symbol,string) lp_iatom"
    and inp :: "('f lp_cut_symbol,nat) lp_atom"
  assumes checked: "lpc_seg_free_check_control fuel P C nds states Fs returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and program: "lp_cut_source_program P"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and represented: "lpc_return_free_module_rep nds states Fs ss control"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpc_triple_answer_contract P (lpc_return_eval eta (states!i)) Q (lp_atom_eval out)"
    and emits: "\<And>i. i<length nds \<Longrightarrow>
      lpc_triple_check_emit Q out (states!i) (fst (receipts!i)) (snd (receipts!i))"
  shows "lpc_triple_answer_contract P ss Q (lp_atom_eval out)"
  unfolding lpc_triple_answer_contract_return_contract
proof (rule lpc_seg_observed_control_contract[where J="lpc_triple_instance_invariant a inp",
    OF checked ranked program invariant lpc_triple_instance_stable lpc_triple_instance_subset
      lpc_triple_instance_scopes represented])
  fix i eta assume index: "i<length nds" and boundary_node: "actions!i=None"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
  show "lpc_return_contract P (lpc_return_eval eta (states!i)) (lpc_answer_model_relation Q) None
    (\<lambda>eta. Some (lp_atom_eval out eta))"
    using boundary[OF index boundary_node known free inv]
    by (simp only: lpc_triple_answer_contract_return_contract)
next
  fix i eta rho tt assume index: "i<length nds"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
    and event: "lpc_answer_transition P (lpc_return_eval eta (states!i)) (Some rho) tt"
  show "(None,Some (lp_atom_eval out rho))\<in>(lpc_answer_model_relation Q)\<^sup>*"
    using lpc_triple_checked_emit[OF emits[OF index] event]
    by (simp only: lpc_answer_model_relation_path)
qed

end
