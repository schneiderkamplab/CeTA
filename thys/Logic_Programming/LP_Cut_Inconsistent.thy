theory LP_Cut_Inconsistent
  imports LP_Cut_Knowledge
begin

fun lp_cut_opposite_guard where
  "lp_cut_opposite_guard (LPCHeadGuard a h b) = LPCHeadGuard a h (\<not>b)"
| "lp_cut_opposite_guard (LPCEqGuard a c b) = LPCEqGuard a c (\<not>b)"

definition lp_cut_check_inconsistent where
  "lp_cut_check_inconsistent guards =
    list_ex (\<lambda>g. lp_cut_opposite_guard g \<in> set guards) guards"

lemma lp_cut_opposite_guard_holds:
  "lp_cut_guard_holds (lp_cut_opposite_guard g) \<eta> = (\<not>lp_cut_guard_holds g \<eta>)"
  by (cases g) auto

theorem lp_cut_checked_inconsistent:
  assumes "lp_cut_check_inconsistent guards"
    "lp_cut_knowledge G guards \<eta>"
  shows False
proof -
  obtain g where g: "g \<in> set guards" "lp_cut_opposite_guard g \<in> set guards"
    using assms(1) by (auto simp: lp_cut_check_inconsistent_def list_ex_iff)
  have both: "lp_cut_guard_holds g \<eta>"
    "lp_cut_guard_holds (lp_cut_opposite_guard g) \<eta>"
    using assms(2) g by (auto simp: lp_cut_knowledge_def list_all_iff)
  show False using both lp_cut_opposite_guard_holds[of g \<eta>] by blast
qed

lemma incompatible_guard_namespaces_are_not_a_contradiction:
  "\<not>lp_cut_check_inconsistent [LPCHeadGuard a b True, LPCEqGuard a b False]"
  by (simp add: lp_cut_check_inconsistent_def)

lemma complementary_guards_are_a_contradiction:
  "lp_cut_check_inconsistent [LPCEqGuard a b True, LPCEqGuard a b False]"
  by (simp add: lp_cut_check_inconsistent_def)

fun lp_cut_guard_refuted where
  "lp_cut_guard_refuted fuel k bindings (LPCHeadGuard a h b) =
    (if b then lp_cut_check_clash fuel k a h else lp_cut_check_match a h bindings)"
| "lp_cut_guard_refuted fuel k bindings (LPCEqGuard a c b) =
    lp_cut_check_equality fuel a c (if b then LPCAlwaysFailure else LPCAlwaysSuccess)"

lemma lp_cut_guard_refuted_sound:
  assumes checked: "lp_cut_guard_refuted fuel k bindings g"
  shows "\<not>lp_cut_guard_holds g \<eta>"
proof (cases g)
  case (LPCHeadGuard a h b)
  show ?thesis
    using checked lp_cut_check_clash_sound[of fuel k a h \<eta>]
      lp_cut_check_match_sound[of a h bindings \<eta>]
    by (cases b) (auto simp: LPCHeadGuard)
next
  case (LPCEqGuard a c b)
  show ?thesis
    using checked lp_cut_equality_failure[of fuel a c \<eta>]
      lp_cut_equality_success[of fuel a c \<eta>]
    by (cases b) (auto simp: LPCEqGuard)
qed

definition lp_cut_check_refuted_guard where
  "lp_cut_check_refuted_guard fuel guards i k bindings =
    (i<length guards \<and> lp_cut_guard_refuted fuel k bindings (guards!i))"

theorem lp_cut_checked_refuted_guard:
  assumes "lp_cut_check_refuted_guard fuel guards i k bindings"
    "lp_cut_knowledge G guards \<eta>"
  shows False
  using assms lp_cut_guard_refuted_sound[of fuel k bindings "guards!i" \<eta>]
  by (auto simp: lp_cut_check_refuted_guard_def lp_cut_knowledge_def list_all_iff)

end
