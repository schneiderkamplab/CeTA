theory LP_Cut_Guards
  imports LP_Cut_Source LP_Source_Tree
begin

definition lp_cut_match_subst where
  "lp_cut_match_subst bindings x = (case map_of bindings x of None \<Rightarrow> Var x | Some t \<Rightarrow> t)"

definition lp_cut_check_match where
  "lp_cut_check_match a h bindings =
    (distinct (map fst bindings) \<and> h\<cdot>lp_cut_match_subst bindings = a)"

theorem lp_cut_check_match_sound:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lp_cut_check_match a h bindings"
  shows "\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
  by (rule lp_cut_head_match_possible[where \<theta>="lp_cut_match_subst bindings"])
    (use checked in \<open>simp add: lp_cut_check_match_def\<close>)

definition lp_cut_check_clash :: "nat \<Rightarrow> nat \<Rightarrow> ('f,string) term \<Rightarrow> ('f,string) term \<Rightarrow> bool" where
  "lp_cut_check_clash fuel k a h =
    ((\<forall>x\<in>vars_term a. length x<k) \<and>
     lp_normalize_goals fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))]
       ([] :: ('f,string) lp_atom list) = Some None)"

theorem lp_cut_check_clash_sound:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lp_cut_check_clash fuel k a h"
  shows "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>)"
proof
  assume "\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
  then obtain \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
    where eq: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>" by blast
  let ?old = "\<lambda>x. lp_isubst (\<eta> x) \<sigma>"
  let ?env = "\<lambda>x. if length x<k then ?old x else \<rho> (drop k x)"
  have a: "lp_ieval a ?env = lp_ieval a ?old"
    by (rule lp_ieval_cong) (use checked in \<open>auto simp: lp_cut_check_clash_def\<close>)
  have h: "lp_ieval (h\<cdot>(\<lambda>x. Var (lp_prefix k x))) ?env = lp_ieval h \<rho>"
    by (simp add: lp_ieval_finite_subst lp_prefix_def)
  have equations: "lp_equations [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))] ?env"
    using eq a h by (simp add: lp_equations_def lp_ieval_subst)
  have normalized: "lp_normalize_goals fuel [(a,h\<cdot>(\<lambda>x. Var (lp_prefix k x)))]
      ([] :: ('f,string) lp_atom list) = Some None"
    using checked by (simp add: lp_cut_check_clash_def)
  show False using lp_normalize_goals_sound[OF normalized equations] by simp
qed

datatype lp_cut_coverage = LPCAlwaysSuccess | LPCAlwaysFailure | LPCBoth

definition lp_cut_check_coverage where
  "lp_cut_check_coverage fuel k a h bindings coverage =
    (case coverage of LPCAlwaysSuccess \<Rightarrow> lp_cut_check_match a h bindings
     | LPCAlwaysFailure \<Rightarrow> lp_cut_check_clash fuel k a h
     | LPCBoth \<Rightarrow> True)"

theorem lp_cut_coverage_success:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lp_cut_check_coverage fuel k a h bindings coverage"
    "coverage=LPCAlwaysSuccess"
  shows "\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>"
  by (rule lp_cut_check_match_sound) (use assms in \<open>simp add: lp_cut_check_coverage_def\<close>)

theorem lp_cut_coverage_failure:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lp_cut_check_coverage fuel k a h bindings coverage"
    "coverage=LPCAlwaysFailure"
  shows "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm. \<exists>\<rho>.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval h \<rho>)"
  by (rule lp_cut_check_clash_sound) (use assms in \<open>simp add: lp_cut_check_coverage_def\<close>)

text \<open>Equality uses one namespace. Renaming its right side as if it were
a clause head would lose sharing and may omit a necessary failure branch.\<close>

definition lp_cut_check_equality ::
  "nat \<Rightarrow> ('f,string) term \<Rightarrow> ('f,string) term \<Rightarrow> lp_cut_coverage \<Rightarrow> bool" where
  "lp_cut_check_equality fuel a b coverage =
    (case coverage of LPCAlwaysSuccess \<Rightarrow> a=b
     | LPCAlwaysFailure \<Rightarrow> lp_normalize_goals fuel [(a,b)]
         ([] :: ('f,string) lp_atom list) = Some None
     | LPCBoth \<Rightarrow> True)"

theorem lp_cut_equality_success:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lp_cut_check_equality fuel a b LPCAlwaysSuccess"
  shows "\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
  using assms by (auto simp: lp_cut_check_equality_def)

theorem lp_cut_equality_failure:
  fixes \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lp_cut_check_equality fuel a b LPCAlwaysFailure"
  shows "\<not>(\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
proof
  assume "\<exists>\<sigma>::string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
  then obtain \<sigma> :: "string \<Rightarrow> ('f,string) lp_iterm"
    where eq: "lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>"
    by blast
  have equations: "lp_equations [(a,b)] (\<lambda>x. lp_isubst (\<eta> x) \<sigma>)"
    using eq by (simp add: lp_equations_def lp_ieval_subst)
  have normalized: "lp_normalize_goals fuel [(a,b)]
      ([] :: ('f,string) lp_atom list) = Some None"
    using checked by (simp add: lp_cut_check_equality_def)
  show False using lp_normalize_goals_sound[OF normalized equations] by simp
qed

end
