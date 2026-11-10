theory LP_Universal_MGU
  imports LP_Unification_Factorisation
begin

text \<open>Caller and clause variables have disjoint tagged namespaces during
unification. The resulting substitutions cover every variable, so the remaining
goals and body cannot be accidentally specialized.\<close>
definition lp_caller_var where "lp_caller_var x = CHR ''0'' # x"
definition lp_clause_var where "lp_clause_var x = CHR ''1'' # x"
definition lp_merge_values where
  "lp_merge_values fallback caller_values rho x = (case x of [] \<Rightarrow> fallback x
    | c#xs \<Rightarrow> if c=CHR ''0'' then caller_values xs else if c=CHR ''1'' then rho xs else fallback x)"
lemma lp_merge_variables[simp]:
  "lp_merge_values fallback caller_values rho (lp_caller_var x) = caller_values x"
  "lp_merge_values fallback caller_values rho (lp_clause_var x) = rho x"
  by (simp_all add: lp_merge_values_def lp_caller_var_def lp_clause_var_def)
lemma lp_merge_domain:
  fixes fallback caller_values rho D x
  shows
  "(\<And>x. D (fallback x)) \<Longrightarrow> (\<And>x. D (caller_values x)) \<Longrightarrow>
    (\<And>x. D (rho x)) \<Longrightarrow> D (lp_merge_values fallback caller_values rho x)"
  by (auto simp: lp_merge_values_def split: list.splits if_splits)
lemma lp_rename_subst:
  "map_term id f t \<cdot> sigma = t \<cdot> (sigma \<circ> f)"
  by (induct t) (auto simp: map_map o_def)
lemma lp_rename_eval:
  "lp_ieval (map_term id f t) eta = lp_ieval t (eta \<circ> f)"
  by (induct t) (auto simp: map_map o_def)

definition lp_universal_mgu ::
  "('f,string) lp_atom \<Rightarrow> ('f,string) lp_atom \<Rightarrow>
    (string \<Rightarrow> ('f,string) term) \<Rightarrow> (string \<Rightarrow> ('f,string) term) \<Rightarrow> bool" where
  "lp_universal_mgu a h sigma rho \<longleftrightarrow>
    lp_atom_subst a sigma = lp_atom_subst h rho \<and>
    (\<forall>(caller_values :: string \<Rightarrow> ('f,string) lp_iterm) nu. lp_atom_eval a caller_values = lp_atom_eval h nu \<longrightarrow>
      (\<exists>delta. (\<forall>x. lp_ieval (sigma x) delta=caller_values x \<and> lp_ieval (rho x) delta=nu x) \<and>
        (\<forall>x. delta x \<in> range caller_values \<union> range nu \<union> range LPIVar)))"

lemma lp_universal_mgu_exists:
  fixes a h :: "('f,string) lp_atom"
    and caller_values nu :: "string \<Rightarrow> ('f,string) term"
  assumes unifies: "lp_atom_subst a caller_values=lp_atom_subst h nu"
  obtains sigma rho where "lp_universal_mgu a h sigma rho"
proof -
  let ?left = "Fun (fst a) (map (map_term id lp_caller_var) (snd a))"
  let ?right = "Fun (fst h) (map (map_term id lp_clause_var) (snd h))"
  let ?theta = "lp_merge_values Var caller_values nu"
  have solution: "?left \<cdot> ?theta=?right \<cdot> ?theta"
    using unifies by (simp add: lp_atom_subst_def lp_rename_subst map_map o_def)
  obtain mu where match: "?left \<cdot> mu=?right \<cdot> mu"
    and factor: "\<And>(eta :: string \<Rightarrow> ('f,string) lp_iterm) x. lp_ieval ?left eta=lp_ieval ?right eta \<Longrightarrow>
      lp_ieval (mu x) eta=eta x"
    by (rule lp_finite_solution_universal_mgu[OF solution]) blast
  let ?sigma = "mu \<circ> lp_caller_var"
  let ?rho = "mu \<circ> lp_clause_var"
  have mgu: "lp_universal_mgu a h ?sigma ?rho"
  proof (unfold lp_universal_mgu_def, intro conjI allI impI)
    show "lp_atom_subst a ?sigma=lp_atom_subst h ?rho"
      using match by (simp add: lp_atom_subst_def lp_rename_subst map_map o_def)
  next
    fix theta gamma :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume equal: "lp_atom_eval a theta=lp_atom_eval h gamma"
    let ?delta = "lp_merge_values LPIVar theta gamma"
    have equal': "lp_ieval ?left ?delta=lp_ieval ?right ?delta"
      using equal by (simp add: lp_atom_eval_def lp_rename_eval map_map o_def)
    have sf: "lp_ieval (?sigma x) ?delta=theta x" for x
      using factor[OF equal', of "lp_caller_var x"] by simp
    have rf: "lp_ieval (?rho x) ?delta=gamma x" for x
      using factor[OF equal', of "lp_clause_var x"] by simp
    have dom: "?delta x\<in>range theta\<union>range gamma\<union>range LPIVar" for x
      by (auto simp: lp_merge_values_def split: list.splits)
    show "\<exists>delta. (\<forall>x. lp_ieval (?sigma x) delta=theta x \<and> lp_ieval (?rho x) delta=gamma x) \<and>
      (\<forall>x. delta x\<in>range theta\<union>range gamma\<union>range LPIVar)"
    proof (rule exI[of _ ?delta], intro conjI)
      show "\<forall>x. lp_ieval (?sigma x) ?delta=theta x \<and> lp_ieval (?rho x) ?delta=gamma x"
        by (intro allI conjI; (rule sf | rule rf))
      show "\<forall>x. ?delta x\<in>range theta\<union>range gamma\<union>range LPIVar"
        by (rule allI; rule dom)
    qed
  qed
  show thesis by (rule that[OF mgu])
qed

end
