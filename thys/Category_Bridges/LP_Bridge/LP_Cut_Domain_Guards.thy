theory LP_Cut_Domain_Guards
  imports LP_Cut_Finite_Unification
begin

text \<open>Coverage checks must justify success in the selected term domain.
An unrestricted-tree success theorem is insufficient when occurs-check failure
would select another alternative. These lemmas retain the executable checks
and prove their stronger, domain-specific meaning.\<close>

definition cut_domain_head ::
  "(('f,string) lp_iterm \<Rightarrow> bool) \<Rightarrow> ('f,string) term \<Rightarrow>
    ('f,string) term \<Rightarrow> (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool" where
  "cut_domain_head D a h eta \<longleftrightarrow>
    (\<exists>s r. (\<forall>x. D (s x)) \<and> (\<forall>x. D (r x)) \<and>
      lp_isubst (lp_ieval a eta) s = lp_ieval h r)"
definition cut_domain_equality ::
  "(('f,string) lp_iterm \<Rightarrow> bool) \<Rightarrow> ('f,string) term \<Rightarrow>
    ('f,string) term \<Rightarrow> (string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool" where
  "cut_domain_equality D a b eta \<longleftrightarrow>
    (\<exists>s. (\<forall>x. D (s x)) \<and>
      lp_isubst (lp_ieval a eta) s = lp_isubst (lp_ieval b eta) s)"

locale cut_substitution_domain =
  fixes D :: "('f,string) lp_iterm \<Rightarrow> bool"
  assumes variables: "\<And>x. D (LPIVar x)"
    and constructors: "\<And>f ts. list_all D ts \<Longrightarrow> D (LPIFun f ts)"
begin

lemma match_success:
  assumes checked: "lp_cut_check_match a h bindings"
    and environment: "\<And>x. D (eta x)"
  shows "cut_domain_head D a h eta"
proof -
  let ?r = "\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta"
  have domain: "\<forall>x. D (?r x)"
    by (intro allI; rule cut_domain_eval[OF environment constructors])
  have matching: "a = h \<cdot> lp_cut_match_subst bindings"
    using checked by (simp add: lp_cut_check_match_def)
  have equation: "lp_isubst (lp_ieval a eta) LPIVar = lp_ieval h ?r"
    by (subst matching) (simp only: lp_isubst_id lp_ieval_finite_subst)
  show ?thesis unfolding cut_domain_head_def
    by (rule exI[of _ LPIVar], rule exI[of _ ?r])
      (simp only: variables domain equation simp_thms)
qed

lemma clash_failure:
  "lp_cut_check_clash fuel k a h \<Longrightarrow> \<not>cut_domain_head D a h eta"
  unfolding cut_domain_head_def using lp_cut_check_clash_sound by blast

lemma equality_success:
  "lp_cut_check_equality fuel a b LPCAlwaysSuccess \<Longrightarrow>
    cut_domain_equality D a b eta"
  unfolding cut_domain_equality_def lp_cut_check_equality_def
  using variables by auto

lemma equality_failure:
  "lp_cut_check_equality fuel a b LPCAlwaysFailure \<Longrightarrow>
    \<not>cut_domain_equality D a b eta"
  unfolding cut_domain_equality_def using lp_cut_equality_failure by blast

lemma coverage_success:
  "lp_cut_check_coverage fuel k a h bindings LPCAlwaysSuccess \<Longrightarrow>
    (\<And>x. D (eta x)) \<Longrightarrow> cut_domain_head D a h eta"
  by (rule match_success) (simp_all add: lp_cut_check_coverage_def)

lemma coverage_failure:
  "lp_cut_check_coverage fuel k a h bindings LPCAlwaysFailure \<Longrightarrow>
    \<not>cut_domain_head D a h eta"
  by (rule clash_failure) (simp add: lp_cut_check_coverage_def)

end

interpretation cut_finite: cut_substitution_domain cut_finite_runtime
  by unfold_locales (rule cut_finite_variable, rule cut_finite_function)
interpretation cut_rational: cut_substitution_domain cut_rational_runtime
  by unfold_locales (rule cut_rational_variable, rule cut_rational_function)

text \<open>The locale premises above are discharged here, not passed to the
user of a certificate. These are coverage lemmas, not yet whole-table
termination corollaries.\<close>

ML \<open>
  val results = @{thms cut_checked_mgu_finite cut_checked_mgu_rational
    cut_finite_domain_iff cut_finite.match_success cut_finite.clash_failure
    cut_finite.equality_success cut_finite.equality_failure
    cut_rational.match_success cut_rational.clash_failure
    cut_rational.equality_success cut_rational.equality_failure}
  val _ = if Thm_Deps.has_skip_proof results then error "LP cut domain proofs: admission" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("LP cut domains: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("LP cut domain oracle dependencies: " ^ commas names)
\<close>
end
