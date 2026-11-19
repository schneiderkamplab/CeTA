theory LP_Checked_Global_MGU
  imports Category_LP_Library.LP_Cut_Scopes LP_Runtime_MGU LP_Cut_Finite_Unification Category_Properties.LP_Domain_Properties
begin

text \<open>Variable occurrence is transported from the shared tree definition.
Clause freshening is injective on the clause variables and avoids the variables
in the active caller terms; saved alternatives keep their separate bindings.\<close>
definition lp_runtime_variables :: "('f,'v) lp_iterm \<Rightarrow> 'v set" where
  "lp_runtime_variables t = {x. logic_subtree (LVar x) (logic_from_native t)}"

definition lp_runtime_freshening ::
  "('v \<Rightarrow> 'v) \<Rightarrow> ('f,'v) lp_iterm list \<Rightarrow> ('f,'v) term list \<Rightarrow> bool" where
  "lp_runtime_freshening r active clause \<longleftrightarrow>
    (let X = \<Union>(lp_runtime_variables ` set active);
         Y = \<Union>(vars_term ` set clause)
     in inj_on r Y \<and> r ` Y \<inter> X = {})"

lemma lp_runtime_variables_variable[simp]:
  "lp_runtime_variables (LPIVar x) = {x}"
  by (auto simp: lp_runtime_variables_def dest: logic_subtree_variable
    intro: logic_subtree.root)
lemma lp_runtime_variables_function[simp]:
  "lp_runtime_variables (LPIFun f ts) = \<Union>(lp_runtime_variables ` set ts)"
  by (auto simp: lp_runtime_variables_def logic_subtree_function)
lemma lp_runtime_variables_embed[simp]:
  "lp_runtime_variables (lp_ieval t LPIVar) = vars_term t"
  by (induct t) (auto simp: image_image)

lemma lp_prefix_freshening:
  assumes short: "\<And>t x. t \<in> set active \<Longrightarrow> x \<in> vars_term t \<Longrightarrow> length x < k"
  shows "lp_runtime_freshening (lp_prefix k) (map (\<lambda>t. lp_ieval t LPIVar) active) clause"
  using short
  by (auto simp: lp_runtime_freshening_def Let_def image_image inj_on_def lp_prefix_def dest: short)

text \<open>The existing solved-substitution check proves the global MGU
condition directly. The competing unifier itself supplies its factor, so no
continuation-dependent approximation of most-generality is needed.\<close>
theorem lp_checked_global_mgu:
  fixes D :: "('f,string) lp_iterm \<Rightarrow> bool"
  assumes variables: "\<And>x. D (LPIVar x)"
    and constructors: "\<And>f ts. list_all D ts \<Longrightarrow> D (LPIFun f ts)"
    and checked: "lpc_check_mgu fuel [(a,b)] V images"
  shows "lp_runtime_mgu D ((),[lp_ieval a LPIVar]) ((),[lp_ieval b LPIVar])
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
proof (rule lp_runtime_mgu_normalized)
  fix x
  show "D (lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
    by (rule cut_domain_eval[OF variables constructors])
next
  show "lp_iatom_subst ((), [lp_ieval a LPIVar])
      (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar) =
    lp_iatom_subst ((), [lp_ieval b LPIVar])
      (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
    using lpc_checked_mgu_unifies[OF checked]
    by (simp add: lp_iatom_subst_def lp_equations_def lp_ieval_subst)
next
  fix u :: "string \<Rightarrow> ('f,string) lp_iterm" and x
  assume eq: "lp_iatom_subst ((), [lp_ieval a LPIVar]) u =
    lp_iatom_subst ((), [lp_ieval b LPIVar]) u"
  have sol: "lp_equations [(a,b)] u"
    using eq by (simp add: lp_iatom_subst_def lp_equations_def lp_ieval_subst)
  show "lp_isubst (lp_ieval (lpc_mgu_substitution V images x) LPIVar) u = u x"
    by (simp add: lp_ieval_subst lpc_checked_mgu_factor[OF checked sol])
qed

lemma lp_cut_terms_mapped:
  "lp_cut_terms (lp_cut_map f g) = map f (lp_cut_terms g)"
  by (cases g) simp_all
lemma lp_cut_terms_scoped:
  "lp_cut_terms (lp_cut_scope_goal r g) = lp_cut_terms g"
  by (cases g) simp_all

definition lp_fresh_resolution ::
  "(('f,'v) lp_iterm \<Rightarrow> bool) \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow>
    ('f,'v) lp_iterm lp_cut_goal list \<Rightarrow> ('f,'v) term \<Rightarrow>
    ('f,'v) term lp_cut_goal list \<Rightarrow>
    ('v \<Rightarrow> ('f,'v) lp_iterm) \<Rightarrow>
    ('v \<Rightarrow> ('f,'v) lp_iterm) \<Rightarrow> bool" where
  "lp_fresh_resolution D a gs h bs sigma rho \<longleftrightarrow>
    (\<exists>r. lp_runtime_freshening r (a # concat (map lp_cut_terms gs))
        (h # concat (map lp_cut_terms bs)) \<and>
      rho = sigma \<circ> r \<and>
      lp_runtime_mgu D ((),[a]) ((),[lp_ieval h (LPIVar \<circ> r)]) sigma)"

lemma lp_fresh_resolution_scope:
  "lp_fresh_resolution D a gs h bs sigma rho \<Longrightarrow>
    lp_fresh_resolution D a (map (lp_cut_scope_goal r) gs) h bs sigma rho"
  by (simp add: lp_fresh_resolution_def map_map o_def lp_cut_terms_scoped)

theorem lp_checked_fresh_resolution:
  fixes D :: "('f,string) lp_iterm \<Rightarrow> bool"
  assumes variables: "\<And>x. D (LPIVar x)"
    and constructors: "\<And>f ts. list_all D ts \<Longrightarrow> D (LPIFun f ts)"
    and checked: "lpc_check_mgu fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] V images"
    and short_a: "\<forall>x\<in>vars_term a. length x<k"
    and short_gs: "lp_cut_short_goals k gs"
  shows "lp_fresh_resolution D (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images (lp_prefix k x)) LPIVar)"
proof -
  have fresh: "lp_runtime_freshening (lp_prefix k)
    (map (\<lambda>t. lp_ieval t LPIVar) (a # concat (map lp_cut_terms gs)))
    (h # concat (map lp_cut_terms bs))"
    by (rule lp_prefix_freshening)
      (use short_a short_gs in \<open>auto simp: lp_cut_short_goals_def\<close>)
  have mgu: "lp_runtime_mgu D ((),[lp_ieval a LPIVar])
    ((),[lp_ieval h (LPIVar \<circ> lp_prefix k)])
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
    using lp_checked_global_mgu[OF variables constructors checked]
    by (simp add: lp_ieval_finite_subst o_def)
  show ?thesis unfolding lp_fresh_resolution_def
    by (intro exI[of _ "lp_prefix k"])
      (use fresh mgu in \<open>simp add: map_map o_def lp_cut_terms_mapped map_concat\<close>)
qed

end
