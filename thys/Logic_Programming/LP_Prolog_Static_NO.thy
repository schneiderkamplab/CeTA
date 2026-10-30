theory LP_Prolog_Static_NO
  imports LP_Prolog_Static
begin

text \<open>For NO, adding error exits is not a sound substitute for dispatch:
an undefined procedure aborts before saved alternatives can run. The source
relation below suppresses ordinary dispatch at builtin and undefined calls.
The static NO bridge proves that neither kind of call is reachable.\<close>

definition lpp_defined where
  "lpp_defined P a = list_ex (\<lambda>c. case fst c of
    Fun (LPCUser f) ts \<Rightarrow> a=(f,length ts) | _ \<Rightarrow> False) P"

definition lpp_undefined where
  "lpp_undefined P s = (\<exists>f ts gs es.
    s=LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs)#es \<and>
      \<not> lpp_defined P (f,length ts))"

definition lp_prolog_source where
  "lp_prolog_source P B X =
    {(s,t)\<in>lp_cut_mgu_source P. \<not>lpp_builtin_active B s \<and> \<not>lpp_undefined P s}
    \<union> {(s,t)\<in>X. lpp_builtin_active B s}
    \<union> {(s,t). lpp_undefined P s \<and> \<not>lpp_builtin_active B s \<and> t=[]}"

lemma lpp_static_no_undefined:
  "lpp_static_state A s \<Longrightarrow> (\<And>a. a\<in>A \<Longrightarrow> lpp_defined P a) \<Longrightarrow>
    \<not> lpp_undefined P s"
  by (auto simp: lpp_undefined_def lpp_static_state_def)

lemma lp_prolog_source_static_step:
  assumes "lpp_static_state A s" "A\<inter>B={}"
    "\<And>a. a\<in>A \<Longrightarrow> lpp_defined P a" "(s,t)\<in>lp_cut_mgu_source P"
  shows "(s,t)\<in>lp_prolog_source P B X"
proof -
  have nb: "\<not>lpp_builtin_active B s"
    by (rule lpp_static_no_builtin[OF assms(1,2)])
  have nu: "\<not>lpp_undefined P s"
    by (rule lpp_static_no_undefined[OF assms(1,3)])
  show ?thesis using assms(4) nb nu by (auto simp: lp_prolog_source_def)
qed

lemma lp_prolog_static_SN_reflection:
  assumes sn: "SN_on (lp_prolog_source P B X) {s}"
    and safe: "lpp_static_state A s" and program: "lpp_static_program A P"
    and disjoint: "A\<inter>B={}"
    and defined: "\<And>a. a\<in>A \<Longrightarrow> lpp_defined P a"
  shows "SN_on (lp_cut_mgu_source P) {s}"
proof -
  have "lpp_static_state A s \<longrightarrow> SN_on (lp_cut_mgu_source P) {s}"
  proof (rule SN_on_induct[OF sn singletonI], intro impI)
    fix x
    assume ih: "\<And>y. (x,y)\<in>lp_prolog_source P B X \<Longrightarrow>
      lpp_static_state A y \<longrightarrow> SN_on (lp_cut_mgu_source P) {y}"
    assume sx: "lpp_static_state A x"
    show "SN_on (lp_cut_mgu_source P) {x}"
      by (rule step_reflects_SN_on)
        (use ih lp_prolog_source_static_step[OF sx disjoint defined]
          lpp_static_mgu_preserved[OF _ program sx] in blast)
  qed
  then show ?thesis using safe by blast
qed

theorem lp_prolog_static_nontermination:
  assumes "\<not> SN_on (lp_cut_mgu_source P) {s}" "lpp_static_state A s"
    "lpp_static_program A P" "A\<inter>B={}"
    "\<And>a. a\<in>A \<Longrightarrow> lpp_defined P a"
  shows "\<not> SN_on (lp_prolog_source P B X) {s}"
  using assms lp_prolog_static_SN_reflection by blast

lemma lp_prolog_source_subset_extension:
  "lp_prolog_source P B X \<subseteq> lp_prolog_extension P B X (lpp_undefined P)"
  by (auto simp: lp_prolog_source_def lp_prolog_extension_def
      lp_prolog_stop_extension_def lpp_undefined_def)

corollary lp_prolog_static_source_termination:
  assumes "SN_on (lp_cut_mgu_source P) {s}" "lpp_static_state A s"
    "lpp_static_program A P" "A\<inter>B={}"
  shows "SN_on (lp_prolog_source P B X) {s}"
  by (rule SN_on_subset1[OF lp_prolog_static_termination[OF assms]
      lp_prolog_source_subset_extension])

end
