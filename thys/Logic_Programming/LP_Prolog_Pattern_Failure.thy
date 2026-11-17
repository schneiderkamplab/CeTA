theory LP_Prolog_Pattern_Failure
 imports LP_Prolog_Pattern_Head LP_Prolog_Scalar_Recurrence_Failure
begin

definition lpp_pattern_value_table where
 "lpp_pattern_value_table H constants observations x =
   (if x\<in>set (lpp_pattern_variables H constants)
    then lpp_scalar_value_table H observations x else None)"

definition lpp_check_pattern_failure where
 "lpp_check_pattern_failure P q observations d H constants guards failure =
   (d<length P \<and> distinct H \<and> length H=length observations \<and>
    length constants=length H \<and>
    fst (P!d)=Fun (LPCUser q) (lpp_pattern_args H constants) \<and>
    take (Suc (length guards)) (snd (P!d)) =
      map lpp_scalar_guard_goal guards @ [lpp_scalar_guard_goal failure] \<and>
    list_all (\<lambda>g. lpp_scalar_guard_check (lpp_pattern_value_table H constants observations) g=Some True) guards \<and>
    lpp_scalar_guard_check (lpp_pattern_value_table H constants observations) failure=Some False)"

lemma lpp_observed_scalar_nth:
 assumes observed: "lpp_scalar_observations operation observations actuals"
   and index: "i<length observations" and entry: "observations!i=Some w"
 shows "lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value w)"
proof -
 have all: "\<forall>k\<in>set [0..<length observations]. case observations!k of None \<Rightarrow> True | Some v \<Rightarrow>
   lpp_stable_scalar_evaluation operation (actuals!k) (lpp_machine_value v)"
   using observed by (simp add: lpp_scalar_observations_def list_all_iff)
 have member: "i\<in>set [0..<length observations]" using index by simp
 show ?thesis using bspec[OF all member] entry by simp
qed

lemma lpp_scalar_observations_substitute:
 assumes observed: "lpp_scalar_observations operation observations actuals"
 shows "lpp_scalar_observations operation observations (map (\<lambda>t. lp_isubst t sigma) actuals)"
proof -
 have lengths: "length actuals=length observations" using observed by (simp add: lpp_scalar_observations_def)
 have each: "lpp_stable_scalar_evaluation operation
   (map (\<lambda>t. lp_isubst t sigma) actuals!i) (lpp_machine_value w)"
   if index: "i<length observations" and entry: "observations!i=Some w" for i w
   using lpp_stable_scalar_evaluation_subst[OF lpp_observed_scalar_nth[OF observed index entry], of sigma]
     index lengths by (simp add: lpp_machine_value_named)
 show ?thesis using lengths each
   by (auto simp: lpp_scalar_observations_def list_all_iff split: option.splits)
qed

lemma lpp_pattern_clause_source:
 assumes step: "(LPCClause gs d mark#saved,t)\<in>lp_cut_mgu_source P"
 shows "(LPCClause gs d mark#saved,t)\<in>lpp_builtin_source P operation"
 using step by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def)

lemma lpp_check_pattern_failure_sound:
 assumes checked: "lpp_check_pattern_failure P q observations d H constants guards failure"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 let ?a = "LPIFun (LPCUser q) actuals"
 let ?h = "Fun (LPCUser q) (lpp_pattern_args H constants)"
 let ?cs = "lpp_pattern_constraints actuals constants"
 let ?table = "lpp_pattern_value_table H constants observations"
 let ?remaining = "drop (Suc (length guards)) (snd (P!d))"
 let ?body = "map lpp_scalar_guard_goal guards @ lpp_scalar_guard_goal failure # ?remaining"
 have index: "d<length P" and distinct: "distinct H"
   and lengths: "length H=length constants" "length actuals=length constants"
   and obs_length: "length H=length observations"
   and successful: "list_all (\<lambda>g. lpp_scalar_guard_check ?table g=Some True) guards"
   and failed: "lpp_scalar_guard_check ?table failure=Some False"
   using checked observed by (auto simp: lpp_check_pattern_failure_def lpp_scalar_observations_def)
 have clause: "P!d=(?h,?body)"
   using checked append_take_drop_id[of "Suc (length guards)" "snd (P!d)"]
   by (cases "P!d") (auto simp: lpp_check_pattern_failure_def)
 show ?thesis
 proof (cases "lpp_solve_head_constraints ?cs")
  case None
  have impossible: "\<not>(\<exists>sigma rho :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm.
      lp_isubst ?a sigma=lp_ieval (fst (P!d)) rho)"
    using lpp_solve_head_constraints_failure[OF None]
      lpp_pattern_unifier_constraints[OF lengths] by (metis clause fst_conv)
  have step: "(LPCClause (LPCAtom ?a#gs) d mark#saved,saved)\<in>lp_cut_mgu_source P"
    by (rule lp_cut_mgu_source.backtrack[OF index impossible])
  show ?thesis by (rule r_into_trancl[OF lpp_pattern_clause_source[OF step]])
 next
  case (Some mu)
  let ?eta = "lpp_partial_arguments H (map (\<lambda>t. lp_isubst t mu) actuals)"
  let ?rho = "lpc_fresh_head_environment (lpp_pattern_variables H constants) ?eta"
  let ?sigma = "\<lambda>x. lp_isubst (mu x) lpc_fresh_caller"
  let ?rest = "map (lp_cut_map (\<lambda>t. lp_isubst t ?sigma)) gs"
  let ?t = "LPCGoals (map (lp_cut_bind mark (\<lambda>t. lp_ieval t ?rho)) ?body @ ?rest)#saved"
  have mgu: "lpc_mgu_resolve ?a gs (fst (P!d)) (snd (P!d)) ?sigma ?rho"
    by (subst clause) (simp only: fst_conv snd_conv; rule lpp_pattern_head_mgu[OF lengths distinct Some])
  have resolved: "(LPCClause (LPCAtom ?a#gs) d mark#saved,?t)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of mark saved]
    by (subst (asm) clause) (simp only: fst_conv snd_conv)
  have source_resolved: "(LPCClause (LPCAtom ?a#gs) d mark#saved,?t)\<in>?R"
    by (rule lpp_pattern_clause_source[OF resolved])
  have substituted: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations
      (map (\<lambda>t. lp_isubst t mu) actuals)"
    by (rule lpp_scalar_observations_substitute[OF observed])
  have parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (?eta x) (lpp_machine_value w)"
    if selected: "?table x=Some w" for x w
    by (rule lpp_scalar_observed_argument[OF obs_length distinct substituted])
      (use selected in \<open>auto simp: lpp_pattern_value_table_def split: if_splits\<close>)
  have covered: "x\<in>set (lpp_pattern_variables H constants)" if "?table x=Some w" for x w
    using that by (auto simp: lpp_pattern_value_table_def split: if_splits)
  have fresh: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (?rho x) (lpp_machine_value w)"
    if "?table x=Some w" for x w
    by (rule lpp_scalar_fresh_parameters[where value_table="?table"])
      (use parameters covered that in auto)
  have body: "(?t,saved)\<in>?R\<^sup>+"
    by (rule lpp_scalar_failed_body[OF successful failed fresh])
  show ?thesis by (rule trancl_trans[OF r_into_trancl[OF source_resolved] body])
 qed
qed

ML \<open>
val checked = [@{thm lpp_check_pattern_failure_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted constructor-headed failure" else ();
\<close>
end
