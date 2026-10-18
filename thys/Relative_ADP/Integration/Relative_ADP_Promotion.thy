theory Relative_ADP_Promotion
  imports Relative_ADP_Integration_Base.Relative_ADP_Integration_Base
begin

datatype 'f relative_adp_root_proof =
    Relative_ADP_Root "'f relative_adp_termination_proof"
  | Relative_ADP_Promote "('f,string) rules" "'f relative_adp_root_proof"

fun check_relative_adp_root ::
  "('f::{compare_order,showl,countable},string) rules \<Rightarrow>
   ('f,string) rules \<Rightarrow> 'f relative_adp_root_proof \<Rightarrow> showsl check" where
  "check_relative_adp_root R B (Relative_ADP_Root p) = check_relative_adp_from_trs R B p"
| "check_relative_adp_root R B (Relative_ADP_Promote S p) = do {
    check (set R \<subseteq> set S \<and> set S \<subseteq> set (R @ B))
      (showsl_lit (STR ''invalid relative promotion split''));
    check_relative_adp_root S (filter (\<lambda>r. r \<notin> set S) B) p
  }"

lemma check_relative_adp_root_sound:
  assumes "isOK (check_relative_adp_root R B p)"
  shows "SN_rel (Trs.rstep (set R)) (Trs.rstep (set B))"
  using assms
proof (induction p arbitrary: R B)
  case (Relative_ADP_Root p)
  then show ?case by (simp add: check_relative_adp_from_trs_sound)
next
  case (Relative_ADP_Promote S p)
  from Relative_ADP_Promote.prems have sub: "set R \<subseteq> set S"
    and child: "isOK (check_relative_adp_root S (filter (\<lambda>r. r \<notin> set S) B) p)"
    by auto
  have filtered: "set (filter (\<lambda>r. r \<notin> set S) B) = set B - set S"
    by auto
  have sn: "SN_rel (Trs.rstep (set S)) (Trs.rstep (set B - set S))"
    using Relative_ADP_Promote.IH[OF child] unfolding filtered .
  have main: "Trs.rstep (set R) \<subseteq> Trs.rstep (set S)"
    by (rule rstep_mono[OF sub])
  have weak: "Trs.rstep (set B) \<subseteq>
      Trs.rstep (set S) \<union> Trs.rstep (set B - set S)"
    unfolding rstep_union[symmetric]
    by (rule rstep_mono) blast
  show ?case by (rule SN_rel_mono'[OF main weak sn])
qed

lemma promotion_rejects_missing_strict_rules:
  assumes "\<not> set R \<subseteq> set S"
  shows "\<not> isOK (check_relative_adp_root R B (Relative_ADP_Promote S p))"
  using assms by simp

lemma promotion_rejects_foreign_rules:
  assumes "\<not> set S \<subseteq> set (R @ B)"
  shows "\<not> isOK (check_relative_adp_root R B (Relative_ADP_Promote S p))"
  using assms by simp

end
