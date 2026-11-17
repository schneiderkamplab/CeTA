theory LP_Cut_Domain_NO_Canonical
  imports LP_Cut_Domain_NO_Finite
begin

lemma cut_goals_forward_back:
  "list_all (cut_goal_shape cut_iatom_shape) gs \<Longrightarrow>
    map cut_igoal (map cut_igoal_back gs) = gs"
  by (auto simp: map_map o_def list_all_iff intro!: map_idI intro: cut_igoal_forward_back)
lemma cut_back_clause_forward:
  assumes "cut_program_shape P" "c<length P"
  shows "cut_head (fst (cut_program_back P!c)) = fst (P!c)"
    "map cut_fgoal (snd (cut_program_back P!c)) = snd (P!c)"
  using arg_cong[OF cut_program_forward_back[OF assms(1)], where f="\<lambda>P. P!c"]
    assms(2) by (auto simp: cut_program_nth dest: arg_cong[where f=fst] arg_cong[where f=snd])
lemma cut_finite_atom_support:
  "cut_finite_runtime (cut_atom a) \<Longrightarrow> t\<in>set (logic_arguments a) \<Longrightarrow>
    finite (logic_variables t)"
  by (cases a) (auto intro!: cut_finite_variable_support dest: cut_finite_arguments[unfolded list_all_iff])

context cut_runtime_domain
begin

text \<open>The inverse simulation uses proved shape, arity and finite-variable
invariants. Its domain-projection premise is discharged separately for the three
term domains; it is not a termination-restriction assumption.\<close>
lemma canonical_no_step:
  assumes step: "(s,t)\<in>mgu_source P"
    and program_shape: "cut_program_shape P"
    and program: "logic_cut_problem A (cut_program_back P) q modes"
    and shape: "list_all (cut_choice_shape cut_iatom_shape) s"
    and finite: "list_all cut_choice_finite s"
    and correct: "logic_runtime_state_correct A (cut_state_back s)"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
  shows "logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
    (cut_state_back s) (cut_state_back t)"
  using step
proof (cases rule: mgu_source.cases)
  case admin
  then show ?thesis by (auto intro: logic_cut_step.admin cut_back_admin)
next
  case (case_call m f ts gs es)
  have fresh: "logic_fresh_mark m (cut_state_back (LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es))"
    by (rule cut_back_fresh) (use case_call in blast)
  show ?thesis using logic_cut_step.case_call[OF fresh[simplified],
      where P="cut_program_back P" and D="\<lambda>u. D (cut_tree u)" and A=A] case_call
    by (simp add: cut_back_slice[OF program_shape] map_map o_def)
next
  case (resolve c a gs sigma rho m es)
  let ?a = "cut_iatom_back a"
  let ?gs = "map cut_igoal_back gs"
  let ?Q = "cut_program_back P"
  have index: "c<length P" using resolve by blast
  have ashape: "cut_iatom_shape a" and gshape: "list_all (cut_goal_shape cut_iatom_shape) gs"
    and eshape: "list_all (cut_choice_shape cut_iatom_shape) es"
    using shape resolve by simp_all
  have atom: "cut_atom ?a = a" by (rule cut_iatom_forward_back[OF ashape])
  have goals: "map cut_igoal ?gs = gs" by (rule cut_goals_forward_back[OF gshape])
  have suffix: "cut_state (cut_state_back es) = es" by (rule cut_state_forward_back[OF eshape])
  have native: "lp_fresh_resolution D (cut_atom ?a) (map cut_igoal ?gs)
      (cut_head (fst (?Q!c))) (map cut_fgoal (snd (?Q!c))) sigma rho"
    using resolve by (simp only: atom goals cut_back_clause_forward[OF program_shape index])
  have caller_atom: "logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) ?a"
    using correct resolve by simp
  have caller: "list_all (logic_tree_arity_correct (logic_symbol_arity A)) (logic_arguments ?a)"
    using caller_atom by (cases ?a) simp
  have head_atom: "logic_atom_correct A (arity_correct (logic_symbol_arity A)) (fst (?Q!c))"
    using program index nth_mem[of c ?Q]
    by (auto simp: logic_cut_problem_def case_prod_unfold)
  have head: "list_all (arity_correct (logic_symbol_arity A)) (logic_arguments (fst (?Q!c)))"
    using head_atom by (cases "fst (?Q!c)") simp
  note lifted = cut_resolution_step[where A=A and P="?Q" and a="?a" and gs="?gs"
    and es="cut_state_back es" and m=m and z=undefined,
    OF _ native caller head projection]
  show ?thesis using lifted index resolve
    by (simp add: goals[unfolded map_map o_def] suffix[unfolded map_map o_def]
      cut_back_clause_forward[OF program_shape index] map_map o_def)
next
  case (backtrack c a gs m)
  let ?a = "cut_iatom_back a"
  let ?gs = "map cut_igoal_back gs"
  let ?Q = "cut_program_back P"
  have index: "c<length P" using backtrack by blast
  have ashape: "cut_iatom_shape a" and gshape: "list_all (cut_goal_shape cut_iatom_shape) gs"
    using shape backtrack by simp_all
  have atom: "cut_atom ?a = a" by (rule cut_iatom_forward_back[OF ashape])
  have goals: "map cut_igoal ?gs = gs" by (rule cut_goals_forward_back[OF gshape])
  have active: "finite (logic_variables u)"
    if active_member: "u\<in>set (logic_arguments ?a @ concat (map logic_goal_terms ?gs))" for u
  proof -
    have af: "cut_finite_runtime (cut_atom ?a)" and gf: "list_all cut_goal_finite (map cut_igoal ?gs)"
      using finite backtrack by (simp_all add: atom goals[unfolded map_map o_def] map_map o_def)
    show ?thesis
    proof (cases "u\<in>set (logic_arguments ?a)")
      case True
      show ?thesis by (rule cut_finite_atom_support[OF af True])
    next
      case False
      obtain g where member: "g\<in>set ?gs" "u\<in>set (logic_goal_terms g)"
        using active_member False by auto
      have fg: "cut_goal_finite (cut_igoal g)" using gf member(1) by (auto simp: list_all_iff)
      show ?thesis by (rule cut_finite_goal_support[OF fg member(2)])
    qed
  qed
  have failure: "\<not>(\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm. \<exists>rho.
      lp_isubst (cut_atom ?a) sigma = lp_ieval (cut_head (fst (?Q!c))) rho)"
    using backtrack by (simp add: atom cut_back_clause_forward[OF program_shape index])
  show ?thesis using cut_backtrack_step[where P="?Q" and A=A and D="\<lambda>u. D (cut_tree u)"
    and gs="?gs" and m=m and es="cut_state_back t", OF _ infinite_UNIV_listI active failure]
    index backtrack by simp
next
  case (unify a b gs sigma es)
  have raw: "logic_mgu (\<lambda>u. D (cut_tree u)) (LAtom () [cut_tree_back a])
      (LAtom () [cut_tree_back b]) (cut_tree_back \<circ> sigma)"
    using unify by (simp add: cut_tree_native.mgu_iff o_def)
  have ca: "logic_tree_arity_correct (logic_symbol_arity A) (cut_tree_back a)"
    and cb: "logic_tree_arity_correct (logic_symbol_arity A) (cut_tree_back b)"
    using correct unify by simp_all
  have typed: "logic_mgu (\<lambda>u. D (cut_tree u) \<and> logic_tree_arity_correct (logic_symbol_arity A) u)
      (LAtom () [cut_tree_back a]) (LAtom () [cut_tree_back b]) (cut_tree_back \<circ> sigma)"
    by (rule logic_mgu_correct_arity[OF raw _ _ projection]) (simp_all add: ca cb)
  have goals: "list_all (cut_goal_shape cut_iatom_shape) gs" using shape unify by simp
  show ?thesis using logic_cut_step.unify[OF typed, where P="cut_program_back P"
      and gs="map cut_igoal_back gs" and es="cut_state_back es"] unify goals
    by (simp add: map_map o_def list_all_iff cut_back_goal_subst cong: map_cong)
next
  case (unify_fail a b gs)
  have failure: "\<not>(\<exists>sigma. logic_substitution_in (\<lambda>u. D (cut_tree u) \<and>
      logic_tree_arity_correct (logic_symbol_arity A) u) sigma \<and>
      logic_subst sigma (cut_tree_back a) = logic_subst sigma (cut_tree_back b))"
  proof
    assume "\<exists>sigma. logic_substitution_in (\<lambda>u. D (cut_tree u) \<and>
      logic_tree_arity_correct (logic_symbol_arity A) u) sigma \<and>
      logic_subst sigma (cut_tree_back a) = logic_subst sigma (cut_tree_back b)"
    then obtain sigma where "logic_subst sigma (cut_tree_back a) = logic_subst sigma (cut_tree_back b)" by blast
    then have "lp_isubst a (cut_tree \<circ> sigma) = lp_isubst b (cut_tree \<circ> sigma)"
      by (metis cut_tree_subst cut_tree_native_roundtrip)
    then show False using unify_fail by blast
  qed
  show ?thesis using logic_cut_step.unify_fail[OF failure, where P="cut_program_back P"
      and gs="map cut_igoal_back gs" and es="cut_state_back t"] unify_fail by simp
next
  case (meta m a gs es body)
  obtain f ts where a: "a=LPIFun f ts" using meta by blast
  have fresh: "logic_fresh_mark m (cut_state_back (LPCGoals (LPCMeta a#gs)#es))"
    by (rule cut_back_fresh) (use meta in blast)
  have lower: "logic_lower m (cut_tree_back a) (map cut_igoal_back body)"
    by (rule cut_back_lower) (use meta in blast)
  show ?thesis using logic_cut_step.meta[OF fresh[unfolded a, simplified]
      lower[unfolded a, simplified], where P="cut_program_back P" and D="\<lambda>u. D (cut_tree u)" and A=A]
    meta a by simp
qed


lemma canonical_no_run:
  fixes sequence :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm lp_cut_entry list"
  assumes steps: "\<And>n. (sequence n,sequence (Suc n))\<in>mgu_source P"
    and program_shape: "cut_program_shape P"
    and program: "logic_cut_problem A (cut_program_back P) q modes"
    and shape: "list_all (cut_choice_shape cut_iatom_shape) (sequence 0)"
    and finite: "list_all cut_choice_finite (sequence 0)"
    and correct: "logic_runtime_state_correct A (cut_state_back (sequence 0))"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
  shows "logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
    (cut_state_back (sequence n)) (cut_state_back (sequence (Suc n)))"
proof -
  have shapes: "list_all (cut_choice_shape cut_iatom_shape) (sequence n)" for n
    by (rule no_run_shape[OF program_shape shape steps])
  have finites: "list_all cut_choice_finite (sequence n)" for n
    by (rule no_run_finite[OF finite steps])
  have corrects: "logic_runtime_state_correct A (cut_state_back (sequence n))" for n
  proof (induct n)
    case 0 show ?case by (rule correct)
  next
    case (Suc n)
    have step: "logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
        (cut_state_back (sequence n)) (cut_state_back (sequence (Suc n)))"
      by (rule canonical_no_step[OF steps program_shape program shapes finites Suc.hyps projection])
    show ?case by (rule logic_cut_step_arity[OF program step Suc.hyps])
  qed
  show ?thesis by (rule canonical_no_step[OF steps program_shape program shapes finites corrects projection])
qed


lemma canonical_no_checked_run:
  assumes checked: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
    and program_shape: "cut_program_shape P"
    and program: "logic_cut_problem A (cut_program_back P) q modes"
    and arguments: "list_all (arity_correct (logic_symbol_arity A)) (map cut_term_back argv)"
    and projection: "\<And>u. D (cut_tree u) \<Longrightarrow>
      D (cut_tree (logic_arity_project (logic_symbol_arity A) undefined u))"
  obtains sequence where
    "sequence 0 = [LogicGoals [LogicAtom (LAtom q (map logic_embed (map cut_term_back argv)))]]"
    "\<And>n. logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
      (sequence n) (sequence (Suc n))"
proof -
  obtain native where start:
      "native 0 = [LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]"
    and transitions: "\<And>n. (native n,native (Suc n))\<in>mgu_source P"
    and finite: "\<And>n. list_all cut_choice_finite (native n)"
    by (rule no_checked_finite_run[OF checked]) blast
  have shape: "list_all (cut_choice_shape cut_iatom_shape) (native 0)"
    by (simp add: start)
  have initial: "cut_state_back (native 0) =
      [LogicGoals [LogicAtom (LAtom q (map logic_embed (map cut_term_back argv)))]]"
    by (simp add: start map_map o_def cut_back_finite)
  have lengths: "length argv = A q"
    using checked program by (simp add: lpc_no_check_source_def logic_cut_problem_def)
  have correct: "logic_runtime_state_correct A (cut_state_back (native 0))"
    using arguments lengths by (simp add: initial list_all_iff)
  have lifted: "logic_cut_step A (\<lambda>u. D (cut_tree u)) (cut_program_back P)
      (cut_state_back (native n)) (cut_state_back (native (Suc n)))" for n
    by (rule canonical_no_run[OF transitions program_shape program shape finite correct projection])
  show thesis by (rule that[of "\<lambda>n. cut_state_back (native n)", OF initial lifted])
qed

end

ML \<open>
  val results = @{thms cut_runtime_domain.canonical_no_step cut_runtime_domain.canonical_no_run
    cut_runtime_domain.canonical_no_checked_run}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut inverse simulation: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Cut inverse simulation: oracle dependencies: " ^ commas names)
\<close>
end
