theory LP_Prolog_Local_Static
  imports LP_Prolog_Identity_Test LP_Prolog_Static_NO
begin

text \<open>A builtin-bearing stem may reach an ordinary recursive component.
Only bodies of clauses that can resolve a predicate in the closed component
must be static. The complete original program remains the semantic subject.\<close>

fun lpp_local_head where
  "lpp_local_head A (Var x) = True"
| "lpp_local_head A (Fun (LPCUser f) ts) = ((f,length ts)\<in>A)"
| "lpp_local_head A (Fun g ts) = False"

definition lpp_local_program where
  "lpp_local_program A P = list_all (\<lambda>c. lpp_local_head A (fst c) \<longrightarrow>
    list_all (lpp_static_template A) (snd c)) P"

lemma lpp_local_head_matches:
  assumes selected: "lpp_static_goal A (LPCAtom a)"
    and match: "lp_isubst a sigma = lp_ieval h rho"
  shows "lpp_local_head A h"
proof -
  obtain f ts where a: "a=LPIFun (LPCUser f) ts" and member: "(f,length ts)\<in>A"
    using selected by auto
  show ?thesis
  proof (cases h)
    case (Var x) then show ?thesis by simp
  next
    case (Fun g us)
    have equal: "LPIFun (LPCUser f) (map (\<lambda>t. lp_isubst t sigma) ts) =
      LPIFun g (map (\<lambda>t. lp_ieval t rho) us)"
      using match by (simp add: a Fun)
    have g: "g=LPCUser f" using equal by simp
    have length: "length us=length ts" using equal by (metis lp_iterm.inject(2) length_map)
    show ?thesis using member by (simp add: Fun g length)
  qed
qed

lemma lpp_local_body_at:
  assumes "lpp_local_program A P" "c<length P"
    "lpp_static_goal A (LPCAtom a)" "lp_isubst a sigma=lp_ieval (fst (P!c)) rho"
  shows "list_all (lpp_static_template A) (snd (P!c))"
  using assms lpp_local_head_matches[OF assms(3,4)]
  by (auto simp: lpp_local_program_def list_all_iff)

lemma lpp_local_source_preserved:
  assumes "(s,t)\<in>lp_cut_source P" "lpp_local_program A P" "lpp_static_state A s"
  shows "lpp_static_state A t"
  using assms
proof (cases rule: lp_cut_source.cases)
  case (resolve c a sigma rho gs m es)
  have selected: "lpp_static_goal A (LPCAtom a)"
    using resolve assms(3) by (simp add: lpp_static_state_def)
  have body: "list_all (lpp_static_template A) (snd (P!c))"
    by (rule lpp_local_body_at[OF assms(2) resolve(3) selected resolve(4)])
  show ?thesis using resolve body assms(3)
    by (auto simp: lpp_static_state_def list_all_iff
      intro: lpp_static_substitute lpp_static_evaluate)
qed (use assms(3) in \<open>auto simp: lpp_static_state_def list_all_iff
  intro: lpp_static_substitute
  dest: lpp_static_admin[unfolded lpp_static_state_def]\<close>)

lemma lpp_local_mgu_preserved:
  "(s,t)\<in>lp_cut_mgu_source P \<Longrightarrow> lpp_local_program A P \<Longrightarrow>
   lpp_static_state A s \<Longrightarrow> lpp_static_state A t"
  using lp_cut_mgu_source_subset lpp_local_source_preserved by blast

lemma lp_prolog_local_SN_reflection:
  assumes sn: "SN_on (lp_prolog_source P B X) {s}"
    and safe: "lpp_static_state A s" and program: "lpp_local_program A P"
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
          lpp_local_mgu_preserved[OF _ program sx] in blast)
  qed
  then show ?thesis using safe by blast
qed

theorem lp_prolog_local_nontermination:
  assumes "\<not> SN_on (lp_cut_mgu_source P) {s}" "lpp_static_state A s"
    "lpp_local_program A P" "A\<inter>B={}"
    "\<And>a. a\<in>A \<Longrightarrow> lpp_defined P a"
  shows "\<not> SN_on (lp_prolog_source P B X) {s}"
  using assms lp_prolog_local_SN_reflection by blast

definition lp_prolog_test_source where
  "lp_prolog_test_source P = lp_prolog_source P lpp_builtin_signature
    (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin)"

lemma lp_prolog_test_source_subset:
  "lp_prolog_test_source P \<subseteq>
    lp_prolog_stop_extension (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin) (lpp_undefined P)"
  by (auto simp: lp_prolog_test_source_def lp_prolog_source_def lp_prolog_stop_extension_def lpp_undefined_def
    intro: lpp_atomic_source.base)

end
