theory LP_Prolog_Attached_Return_Leaf
 imports LP_Prolog_Leaf_Coverage_Code
begin

lemma lpp_runtime_fresh_body_separates_observer:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and body: "x\<in>lpc_body_only_variables h bs"
 and finite_goals: "lpp_finite_goals gs"
 and finite_before: "lpp_finite_term u"
 and finite_after: "lpp_finite_term (lp_isubst u sigma)"
 and covered: "set2_lp_iterm u \<subseteq>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "set2_lp_iterm (rho x) \<inter> set2_lp_iterm (lp_isubst u sigma)={}"
proof -
 obtain qs where goals: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_goals] by blast
 obtain t where observer: "u=lp_ieval t LPIVar"
  using lpp_finite_runtime_template[OF finite_before] by blast
 have support: "vars_term t \<subseteq> (\<Union>g\<in>set qs. \<Union>v\<in>set (lp_cut_terms g). vars_term v)"
  using covered unfolding observer goals[symmetric]
  by (simp add: lpp_template_runtime_support lpp_evaluated_goals_runtime_support lpp_finite_goal_map)
 have finite: "lpp_finite_term (lp_ieval t sigma)"
  using finite_after by (simp add: observer lp_ieval_subst)
 have separated: "set2_lp_iterm (rho x) \<inter> set2_lp_iterm (sigma v)={}"
  if member: "v\<in>vars_term t" for v
 proof -
  have live: "v\<in>(\<Union>g\<in>set qs. \<Union>w\<in>set (lp_cut_terms g). vars_term w)"
   using support member by blast
  have image_finite: "lpp_finite_term (sigma v)"
   by (rule lpp_finite_eval_variable[OF member finite])
  show ?thesis using lpp_mgu_body_only_separate_live_caller[
    OF mgu[unfolded goals[symmetric]] body live]
    image_finite by simp
 qed
 show ?thesis using separated
  by (auto simp: observer lp_ieval_subst lpp_evaluation_runtime_support)
qed

lemma lpp_attached_slot_runtime_coverage:
 assumes live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "set2_lp_iterm (eta slot) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
     \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 using live by (auto simp: lpp_finite_goal_map lpp_evaluation_runtime_support)

lemma lpp_attached_matching_acquires_leaf_separation:
 fixes eta :: "nat \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest) h bs sigma rho"
 and matching: "lp_ieval h nu=a"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and body: "x\<in>lpc_body_only_variables h bs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (eta slot)"
 shows "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (eta slot) sigma) \<and>
   set2_lp_iterm (rho x) \<inter> set2_lp_iterm (lp_isubst (eta slot) sigma)={}"
proof -
 have support: "set2_lp_iterm (eta slot) \<subseteq>
   (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
    \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_attached_slot_runtime_coverage[OF live])
 have bounded: "lpp_bounded_images {u. vars_term u={}} sigma (set2_lp_iterm (eta slot))"
  by (rule lpp_runtime_matching_leaf_images[OF mgu matching finite_call finite_rest]) (use support in blast)
 have leaf: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lp_isubst (eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known bounded]) simp
 have separated: "set2_lp_iterm (rho x) \<inter> set2_lp_iterm (lp_isubst (eta slot) sigma)={}"
  by (rule lpp_runtime_fresh_body_separates_observer[OF mgu body finite_rest
    lpp_runtime_leaf_effect_finite[OF known] lpp_runtime_leaf_effect_finite[OF leaf] support])
 show ?thesis using leaf separated by simp
qed

lemma lpp_leaf_stack_attachment:
 "lpp_leaf_stack_invariant A specs (lpc_attach_answers rest ss) = lpp_leaf_stack_invariant A specs ss"
 by (auto simp: lpp_leaf_stack_invariant_def lpc_attach_answers_def list_all_iff)

lemma lpp_attached_matching_leaf_base_step:
 fixes eta :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   ((LPCClause (LPCAtom a#gs) c m,eta)#saved)"
 and matching: "lp_ieval (fst (P!c)) nu=a"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)"
 and live: "set (map fst specs) \<subseteq>
   (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof -
 have attached: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved))"
   using invariant by (simp only: lpp_leaf_stack_attachment)
 show ?thesis
 proof (rule lpp_leaf_stack_base_step[OF step attached])
 fix a' gs' c' m' ret es sigma rho
 assume shape: "lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved) =
   (LPCClause (LPCAtom a'#gs') c' m',ret)#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have actual: "lpc_mgu_resolve a (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)
   (fst (P!c)) (snd (P!c)) sigma rho"
 and ret: "ret=eta"
  using shape mgu by (auto simp: lpc_attach_answers_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
 proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
  fix slot initial_shape
  assume member: "(slot,initial_shape)\<in>set specs"
   and known: "lpp_runtime_leaf_effect {u. vars_term u={}} initial_shape (ret slot)"
  have occurrence: "slot\<in>(\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
   using live member by force
  have support: "set2_lp_iterm (eta slot) \<subseteq>
    set2_lp_iterm a \<union> (\<Union>g\<in>set (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
   using lpp_attached_slot_runtime_coverage[OF occurrence, of eta gs] by blast
  show "lpp_runtime_leaf_effect {u. vars_term u={}} initial_shape (lp_isubst (ret slot) sigma)"
   by (rule lpp_runtime_leaf_effect_substitute[OF known])
    (use lpp_runtime_matching_leaf_images[OF actual matching finite_call finite_rest support] ret in auto)
 qed
next
 fix a' b' gs' ret es sigma
 assume "lpc_attach_answers rest ((LPCClause (LPCAtom a#gs) c m,eta)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 then show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  by (simp add: lpc_attach_answers_def)
qed

qed

definition lpp_check_attached_leaf_slots where
 "lpp_check_attached_leaf_slots slots rest = (set slots \<subseteq> lpp_leaf_goals_variables rest)"

lemma lpp_check_attached_leaf_slots_sound:
 "lpp_check_attached_leaf_slots (map fst specs) rest \<Longrightarrow>
  set (map fst specs) \<subseteq> (\<Union>g\<in>set rest. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 by (simp add: lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)

lemma lpp_attached_slots_positive:
 "lpp_check_attached_leaf_slots [0::nat,2] [LPCAtom (Fun f [Var 0, Var 2])]"
 by (simp add: lpp_check_attached_leaf_slots_def)

lemma lpp_attached_slots_missing_return_rejected:
 "\<not>lpp_check_attached_leaf_slots [0::nat,1] [LPCAtom (Fun f [Var 0, Var 2])]"
 by (simp add: lpp_check_attached_leaf_slots_def)

lemma lpp_attached_slots_missing_continuation_rejected:
 "\<not>lpp_check_attached_leaf_slots [slot] []"
 by (simp add: lpp_check_attached_leaf_slots_def)

ML \<open>
val checked = @{thms lpp_runtime_fresh_body_separates_observer lpp_attached_slot_runtime_coverage
 lpp_attached_matching_acquires_leaf_separation lpp_leaf_stack_attachment lpp_attached_matching_leaf_base_step
 lpp_check_attached_leaf_slots_sound lpp_attached_slots_positive
 lpp_attached_slots_missing_return_rejected lpp_attached_slots_missing_continuation_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached return leaf transport" else ();
\<close>
end
