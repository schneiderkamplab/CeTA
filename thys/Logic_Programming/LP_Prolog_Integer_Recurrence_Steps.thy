theory LP_Prolog_Integer_Recurrence_Steps
  imports LP_Prolog_Integer_Source LP_Source_Recurrent_Simulation
begin

text \<open>Exact successful and failed arithmetic steps for the inverse source
simulation. These use the existing interpreted integer operations. In particular,
a failed guard resumes the saved alternative stack, rather than erasing it.\<close>

lemma lpp_integer_recurrence_builtin_success:
  assumes outcome: "lpp_integer_source_builtin f ts (LPPBuiltinSuccess mu)"
  shows "(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
  using lpp_atomic_source.success[where U=lpp_integer_source_builtin and P=P and B=lpp_builtin_signature and gs=gs and es=es, OF outcome]
    lpp_integer_source_selected[OF outcome]
  by (auto simp: lp_prolog_source_def lpp_builtin_active_def)

lemma lpp_integer_recurrence_builtin_failure:
  assumes outcome: "lpp_integer_source_builtin f ts LPPBuiltinFailure"
  shows "(LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es,es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
  using lpp_atomic_source.failure[where U=lpp_integer_source_builtin and P=P and B=lpp_builtin_signature and gs=gs and es=es, OF outcome]
    lpp_integer_source_selected[OF outcome]
  by (auto simp: lp_prolog_source_def lpp_builtin_active_def)

lemma lpp_integer_recurrence_assignment:
  assumes evaluated: "lpp_integer_evaluation e n"
    and unifier: "lpp_integer_unifier a n=Some mu"
  shows "(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t mu)) gs)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof (rule lpp_integer_recurrence_builtin_success)
  show "lpp_integer_source_builtin ''2:is'' [a,e] (LPPBuiltinSuccess mu)"
    by (simp only: lpp_integer_source_is lpp_integer_is_outcome_exact[OF evaluated]
      unifier option.case)
qed

lemma lpp_integer_recurrence_comparison_outcome:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
  shows "lpp_integer_source_builtin f [a,b]
    (if lpp_integer_compare comparison (if reversed then m else n) (if reversed then n else m)
     then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
  by (simp only: lpp_integer_source_comparison[OF descriptor left right];
      cases reversed; simp only: if_True if_False
        lpp_integer_compare_outcome_exact[OF left right]
        lpp_integer_compare_outcome_exact[OF right left])

lemma lpp_integer_recurrence_comparison_success:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
    and holds: "lpp_integer_compare comparison (if reversed then m else n) (if reversed then n else m)"
  shows "(LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs)#es,LPCGoals gs#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  have outcome: "lpp_integer_source_builtin f [a,b] (LPPBuiltinSuccess LPIVar)"
    using lpp_integer_recurrence_comparison_outcome[OF descriptor left right] holds by simp
  show ?thesis using lpp_integer_recurrence_builtin_success[OF outcome, of gs es P] by simp
qed

lemma lpp_integer_recurrence_comparison_failure:
  assumes descriptor: "lpp_comparison_descriptor f comparison reversed"
    and left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
    and fails: "\<not>lpp_integer_compare comparison (if reversed then m else n) (if reversed then n else m)"
  shows "(LPCGoals (LPCAtom (LPIFun (LPCUser f) [a,b])#gs)#es,es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  have outcome: "lpp_integer_source_builtin f [a,b] LPPBuiltinFailure"
    using lpp_integer_recurrence_comparison_outcome[OF descriptor left right] fails by simp
  show ?thesis by (rule lpp_integer_recurrence_builtin_failure[OF outcome])
qed

lemma lpp_integer_recurrence_first_clause_steps:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),bs)"
    and ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
    and fresh: "\<And>x. x\<notin>set xs \<Longrightarrow> rho x=LPIVar x"
    and ordinary: "(f,length xs)\<notin>lpp_builtin_signature"
  shows "\<exists>m. (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es,
    LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)] d m) cs @
        LPCBarrier m#es))\<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
proof -
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var xs)) rho"
  let ?s = "LPCGoals [LPCAtom ?a]#es"
  obtain m where selected: "(?s,LPCClause [LPCAtom ?a] c m#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es))\<in>lp_cut_mgu_source P"
    and resolved: "(LPCClause [LPCAtom ?a] c m#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es),
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es))\<in>lp_cut_mgu_source P"
    using lpc_ground_first_clause_transition_pair[OF first index clause ground fresh] by blast
  have defined: "lpp_defined P (f,length xs)"
    unfolding lpp_defined_def list_ex_iff
    by (rule bexI[of _ "P!c"]) (use nth_mem[OF index] clause in auto)
  have selected_source: "(?s,LPCClause [LPCAtom ?a] c m#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es))
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using selected ordinary defined
    by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  have resolved_source: "(LPCClause [LPCAtom ?a] c m#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es),
      LPCGoals (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) bs)#
      (map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es))
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
    using resolved
    by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)
  show ?thesis using selected_source resolved_source
    by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpc_ground_head_fresh_body_mgu},
  @{thm lpc_ground_first_clause_steps}, @{thm lpp_integer_recurrence_first_clause_steps}, @{thm lp_source_nontermination_simulation},
  @{thm lpp_integer_recurrence_assignment}, @{thm lpp_integer_recurrence_comparison_success},
  @{thm lpp_integer_recurrence_comparison_failure}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm lpp_integer_source_comparison},
  @{thm lpp_integer_is_outcome_exact}, @{thm lpc_uniform_recursion_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted integer recurrence simulation dependency" else ();
val _ = writeln ("RECURRENCE_ORACLES: " ^ commas (oracles checked));
\<close>
end
