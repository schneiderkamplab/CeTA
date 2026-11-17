theory LP_Cut_Domain_Precise_Canonical
  imports LP_Cut_Domain_Precise_MGU
begin

context cut_runtime_domain
begin

lemma precise_canonical_step:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem snd (cut_rank_program P) p modes"
    and erasure: "cut_mgu_erasure D"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and correct: "logic_runtime_state_correct snd s"
    and step: "logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) s t"
  shows "(cut_erased_state s,cut_erased_state t) \<in> precise_source (cut_program P)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  show ?thesis by (rule precise_source.admin) (simp only: cut_erased_admin admin option.map)
next
  case (case_call m f ts gs es)
  obtain f0 k where f: "f=(f0,k)" by (cases f) auto
  have len: "length ts=k" using correct case_call by (simp add: f)
  have fresh: "lp_cut_fresh m (cut_erased_state (LogicGoals (LogicAtom (LAtom f ts)#gs)#es))"
    using case_call by (simp only: cut_erased_fresh)
  show ?thesis using precise_source.case_call[OF fresh[unfolded f, simplified], where P="cut_program P"] case_call
    by (simp add: f len cut_rank_slice cut_slice map_map o_def)
next
  case (resolve c ren a gs sigma m es)
  have original_index: "c<length P" using resolve by (simp add: cut_rank_program_def)
  have index: "c<length (cut_program P)" using original_index by simp
  have eval_comp: "logic_subst sigma \<circ> logic_eval (LVar \<circ> ren) = logic_eval (sigma \<circ> ren)"
    by (rule ext) (simp add: logic_subst_composition o_def)
  have caller: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
    using correct resolve by simp
  have head_finite: "logic_atom_correct snd (arity_correct (logic_symbol_arity snd))
      (cut_rank_atom (fst (P!c)))"
    using program nth_mem[of c "cut_rank_program P"] original_index
    by (auto simp: logic_cut_problem_def cut_rank_program_def case_prod_unfold)
  have head: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd))
      (logic_atom_map (logic_eval (LVar \<circ> ren)) (cut_rank_atom (fst (P!c))))"
    using head_finite by (cases "cut_rank_atom (fst (P!c))")
      (auto simp: list_all_iff intro: logic_subst_arity_correct)
  have fresh: "logic_freshening ren (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (cut_rank_atom (fst (P!c))) @ concat (map logic_goal_terms (map cut_rank_goal (snd (P!c)))))"
    using resolve by (simp add: cut_rank_program_nth[OF original_index])
  have mgu: "logic_mgu (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) a
      (logic_atom_map (logic_eval (LVar \<circ> ren)) (cut_rank_atom (fst (P!c)))) sigma"
    using resolve by (simp add: cut_rank_program_nth[OF original_index])
  have native: "mgu_resolve (cut_atom (cut_unrank_atom a)) (map cut_igoal (map cut_unrank_goal gs))
      (fst (cut_program P!c)) (snd (cut_program P!c))
      (cut_tree \<circ> cut_unrank_tree \<circ> sigma) ((cut_tree \<circ> cut_unrank_tree \<circ> sigma) \<circ> ren)"
    unfolding cut_program_nth[OF original_index] fst_conv snd_conv
    by (rule erased_mgu_resolve[OF erasure fresh caller head mgu])
  show ?thesis using precise_source.resolve[OF index native,
    where m=m and es="cut_erased_state es"] resolve
    by (simp add: cut_program_nth[OF original_index] cut_rank_program_nth[OF original_index]
      eval_comp map_map o_def cut_unrank_goal_eval_bind cut_unrank_goal_subst
      cut_goal_subst cut_goal_eval_bind logic_subst_composition cut_atom_selectors)
next
  case (backtrack c ren a gs m)
  have original_index: "c<length P" using backtrack by (simp add: cut_rank_program_def)
  have index: "c<length (cut_program P)" using original_index by simp
  have head_atom: "logic_atom_correct snd (arity_correct (logic_symbol_arity snd))
      (cut_rank_atom (fst (P!c)))"
    using program nth_mem[of c "cut_rank_program P"] original_index
    by (auto simp: logic_cut_problem_def cut_rank_program_def case_prod_unfold)
  have head: "list_all (arity_correct (logic_symbol_arity snd)) (logic_arguments (cut_rank_atom (fst (P!c))))"
    using head_atom by (cases "cut_rank_atom (fst (P!c))") simp
  have caller: "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
    using correct backtrack by (simp add: cut_atom_selectors)
  have fresh: "logic_freshening ren (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (cut_rank_atom (fst (P!c))) @ concat (map logic_goal_terms (map cut_rank_goal (snd (P!c)))))"
    using backtrack by (simp add: cut_rank_program_nth[OF original_index])
  have failed: "\<not>(\<exists>sigma. logic_substitution_in (\<lambda>t. D (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) sigma \<and>
    logic_atom_map (logic_subst sigma) a =
      logic_atom_map (logic_subst sigma \<circ> logic_eval (LVar \<circ> ren)) (cut_rank_atom (fst (P!c))))"
    using backtrack by (simp add: cut_rank_program_nth[OF original_index])
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
    (\<forall>x. D (sigma x)) \<and> (\<forall>x. D (rho x)) \<and>
    lp_isubst (cut_atom (cut_unrank_atom a)) sigma = lp_ieval (fst (cut_program P!c)) rho)"
    unfolding cut_program_nth[OF original_index] fst_conv
    by (rule ranked_fresh_failure[OF fresh caller head projection failed])
  show ?thesis using precise_source.backtrack[OF index failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and m=m and es="cut_erased_state t"] backtrack by (simp add: cut_atom_selectors)
next
  case (unify a b sigma gs es)
  have ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    using correct unify by simp_all
  have native: "mgu_unify (cut_tree (cut_unrank_tree a)) (cut_tree (cut_unrank_tree b))
    (map cut_igoal (map cut_unrank_goal gs)) (cut_tree \<circ> cut_unrank_tree \<circ> sigma)"
    by (rule erased_mgu_unify[OF erasure ca cb]) (use unify in auto)
  show ?thesis using precise_source.unify[OF native, where es="cut_erased_state es"] unify
    by (simp add: map_map o_def cut_unrank_goal_subst cut_goal_subst)
next
  case (unify_fail a b gs)
  have ca: "logic_tree_arity_correct (logic_symbol_arity snd) a"
    and cb: "logic_tree_arity_correct (logic_symbol_arity snd) b"
    using correct unify_fail by simp_all
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    (\<forall>x. D (sigma x)) \<and> lp_isubst (cut_tree (cut_unrank_tree a)) sigma =
      lp_isubst (cut_tree (cut_unrank_tree b)) sigma)"
    by (rule ranked_equalizer_failure[OF ca cb projection]) (use unify_fail in auto)
  show ?thesis using precise_source.unify_fail[OF failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state t"] unify_fail by simp
next
  case (meta m f ts gs es body)
  have fresh: "lp_cut_fresh m (cut_erased_state (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    using meta by (simp only: cut_erased_fresh)
  have lower: "lp_cut_lower m (cut_tree (cut_unrank_tree (LFun f ts)))
      (map cut_igoal (map cut_unrank_goal body))"
    by (rule cut_lower, rule cut_unrank_lower) (use meta in blast)
  show ?thesis using precise_source.meta[OF _ lower,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] meta fresh by simp
next
  case (meta_diverges a gs es)
  have failure: "\<not>(\<exists>m body. lp_cut_lower m (cut_tree (cut_unrank_tree a)) body)"
    by (rule cut_diverges_unlowerable, rule cut_unrank_lower_diverges) (use meta_diverges in blast)
  show ?thesis using precise_source.meta_unlowerable[OF failure,
    where gs="map cut_igoal (map cut_unrank_goal gs)" and es="cut_erased_state es"] meta_diverges by simp
qed

theorem precise_canonical_termination:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "logic_cut_problem snd (cut_rank_program P) p modes"
    and erasure: "cut_mgu_erasure D"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and native: "\<And>ts :: (('f \<times> nat) logic_symbol,string) fo_term list.
      logic_query (logic_symbol_arity snd) (LogicUser p) modes (LAtom (LogicUser p) ts) \<Longrightarrow>
      SN_on (precise_source (cut_program P)) {cut_erased_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]}"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) p modes"
proof (unfold logic_cut_terminates_in_def, clarify)
  fix ts s assume query: "logic_query (logic_symbol_arity snd) (LogicUser p) modes (LAtom (LogicUser p) ts)"
    and init: "s 0 = [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]"
    and steps: "\<forall>n. logic_cut_step snd (\<lambda>t. D (cut_tree (cut_unrank_tree t))) (cut_rank_program P) (s n) (s (Suc n))"
  have start_correct: "logic_runtime_state_correct snd (s 0)"
    using query by (simp add: init logic_query_def list_all_iff)
  have correct: "logic_runtime_state_correct snd (s n)" for n
    by (rule logic_cut_run_arity[where run=s and D="\<lambda>t. D (cut_tree (cut_unrank_tree t))", OF program start_correct]) (use steps in simp)
  have chain: "\<forall>n. ((cut_erased_state \<circ> s) n,(cut_erased_state \<circ> s) (Suc n)) \<in> precise_source (cut_program P)"
    proof (intro allI)
    fix n
    show "((cut_erased_state \<circ> s) n,(cut_erased_state \<circ> s) (Suc n)) \<in> precise_source (cut_program P)"
      unfolding o_apply by (rule precise_canonical_step[OF program erasure _ correct]) (use projection steps in auto)
  qed
  have bad: "\<exists>f. f 0 \<in> {cut_erased_state [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]]} \<and>
      (\<forall>n. (f n,f (Suc n)) \<in> precise_source (cut_program P))"
    by (rule exI[of _ "cut_erased_state \<circ> s"], rule conjI) (simp add: init, rule chain)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed


text \<open>All precise checker families share the same ranked-query erasure.
Their native soundness theorem supplies the sole family-specific premise.\<close>
theorem precise_native_termination:
  fixes P :: "('f,string) logic_cut_program"
  assumes program: "cut_control_program P"
    and erasure: "cut_mgu_erasure D"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
    and native: "\<And>ts :: ('f lp_cut_symbol,string) term list.
      length ts = length modes \<Longrightarrow>
      (\<And>i. i \<in> set (lpc_positions modes) \<Longrightarrow> ground (ts!i)) \<Longrightarrow>
      SN_on (precise_source (cut_program P))
        {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program P) (q,length modes) modes"
proof (rule precise_canonical_termination[OF _ erasure projection])
  show "logic_cut_problem snd (cut_rank_program P) (q,length modes) modes"
    using program by (simp add: cut_rank_problem)
next
  fix ts :: "(('f \<times> nat) logic_symbol,string) fo_term list"
  assume query: "logic_query (logic_symbol_arity snd) (LogicUser (q,length modes)) modes
    (LAtom (LogicUser (q,length modes)) ts)"
  have len: "length (map (cut_term \<circ> cut_unrank_term) ts) = length modes"
    using query by (simp add: logic_query_def)
  have grounds: "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t) (zip ts modes)"
    using query unfolding logic_query_def by simp
  have gr: "ground (map (cut_term \<circ> cut_unrank_term) ts!i)"
    if "i\<in>set (lpc_positions modes)" for i
  proof -
    have i: "i < length modes" and mode: "modes!i" using that
      by (simp_all add: lpc_positions_def)
    have it: "i < length ts" using i len by simp
    have pair: "(ts!i,modes!i) \<in> set (zip ts modes)"
      using i it by (auto simp: in_set_zip)
    have "logic_ground (ts!i)"
      using list_all_iff[THEN iffD1, OF grounds] pair mode by auto
    then show ?thesis by (simp add: it cut_term_ground[symmetric])
  qed
  have native: "SN_on (precise_source (cut_program P))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q)
      (map (\<lambda>t. lp_ieval t LPIVar) (map (cut_term \<circ> cut_unrank_term) ts)))]]}"
    by (rule native[OF len gr])
  show "SN_on (precise_source (cut_program P))
    {cut_erased_state [LogicGoals [LogicAtom (LAtom (q,length modes) (map logic_embed ts))]]}"
    using native by (simp add: map_map o_def cut_unrank_embed cut_tree_embed)
qed

end
ML \<open>
  val results = @{thms cut_runtime_domain.precise_canonical_step cut_runtime_domain.precise_canonical_termination cut_runtime_domain.precise_native_termination}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked forward simulation: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked forward simulation: oracle dependency"
\<close>
end
