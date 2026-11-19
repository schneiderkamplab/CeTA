theory LP_Cut_Domain_Knowledge
  imports Category_LP_Bridge.LP_Cut_Domain_Guards Category_LP_Library.LP_Cut_Interface
    Category_LP_Library.LP_Cut_Inconsistent
begin

text \<open>The same executable guard, interface and instance checks are
interpreted in each substitution domain. Knowledge includes the domain of the
valuation, so links cannot silently introduce unrestricted-tree values.\<close>

context cut_substitution_domain
begin

fun guard_holds where
  "guard_holds (LPCHeadGuard a h b) eta = (cut_domain_head D a h eta = b)"
| "guard_holds (LPCEqGuard a c b) eta = (cut_domain_equality D a c eta = b)"
definition knowledge where
  "knowledge G guards eta \<longleftrightarrow>
    (\<forall>x. D (eta x)) \<and> (\<forall>x\<in>G. lp_seg_ground (eta x)) \<and>
    list_all (\<lambda>g. guard_holds g eta) guards"

lemma knowledge_domain:
  "knowledge G guards eta \<Longrightarrow> D (eta x)"
  by (simp add: knowledge_def)
lemma valuation_domain:
  "(\<And>x. D (eta x)) \<Longrightarrow> D (lp_ieval t eta)"
  by (rule cut_domain_eval) (auto intro: constructors)

lemma guard_subst:
  "guard_holds (lp_cut_guard_subst mu g) eta =
    guard_holds g (\<lambda>x. lp_ieval (mu x) eta)"
  by (cases g) (simp_all add: cut_domain_head_def cut_domain_equality_def lp_ieval_finite_subst)

lemma opposite_guard:
  "guard_holds (lp_cut_opposite_guard g) eta = (\<not>guard_holds g eta)"
  by (cases g) auto
lemma inconsistent:
  "lp_cut_check_inconsistent guards \<Longrightarrow> knowledge G guards eta \<Longrightarrow> False"
  using opposite_guard
  by (auto simp: lp_cut_check_inconsistent_def knowledge_def list_ex_iff list_all_iff; blast)

lemma refuted_guard:
  assumes checked: "lp_cut_guard_refuted fuel k bindings g"
    and domain: "\<And>x. D (eta x)"
  shows "\<not>guard_holds g eta"
proof (cases g)
  case (LPCHeadGuard a h b)
  show ?thesis using checked match_success[OF _ domain, where a=a and h=h and bindings=bindings]
    clash_failure[of fuel k a h eta]
    by (cases b) (auto simp: LPCHeadGuard)
next
  case (LPCEqGuard a c b)
  show ?thesis using checked equality_success[of fuel a c eta]
    equality_failure[of fuel a c eta]
    by (cases b) (auto simp: LPCEqGuard)
qed
lemma checked_refuted_guard:
  "lp_cut_check_refuted_guard fuel guards i k bindings \<Longrightarrow>
    knowledge G guards eta \<Longrightarrow> False"
  using refuted_guard[where fuel=fuel and k=k and bindings=bindings and g="guards!i" and eta=eta]
  by (auto simp: lp_cut_check_refuted_guard_def knowledge_def list_all_iff)

theorem instance_knowledge:
  assumes checked: "lp_cut_check_instance s G guards t H guards' bindings swaps"
    and knowledge: "knowledge (set G) guards \<eta>"
  shows "knowledge (set H) guards'
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) \<eta>)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  have ground: "\<forall>x\<in>set H. lp_seg_ground (lp_ieval (?mu x) \<eta>)"
    using checked knowledge
    by (auto simp: lp_cut_check_instance_def Let_def knowledge_def
      lp_seg_ground_eval list_all_iff; blast)
  have guards: "\<And>g. g\<in>set guards' \<Longrightarrow>
    guard_holds g (\<lambda>x. lp_ieval (?mu x) \<eta>)"
  proof -
    fix g assume member: "g\<in>set guards'"
    have in_source: "lp_cut_guard_subst ?mu g\<in>set guards"
      using checked member by (auto simp: lp_cut_check_instance_def Let_def list_all_iff)
    have "guard_holds (lp_cut_guard_subst ?mu g) \<eta>"
      using knowledge in_source by (auto simp: knowledge_def list_all_iff)
    then show "guard_holds g (\<lambda>x. lp_ieval (?mu x) \<eta>)"
      by (simp only: guard_subst)
  qed
  have domain: "\<forall>x. D (lp_ieval (?mu x) \<eta>)"
    by (intro allI; rule valuation_domain; rule knowledge_domain[OF knowledge])
  show ?thesis using ground guards domain by (auto simp: knowledge_def list_all_iff)
qed

theorem interface_knowledge:
  assumes checked: "lp_cut_check_interface fuel eqs vs ts s G guards t H guards'"
    and equations: "lp_equations eqs \<eta>"
    and knowledge: "knowledge (set G) guards \<eta>"
  shows "knowledge (set H) guards' \<eta>"
proof -
  let ?mu = "lp_cut_instance_subst (zip vs ts)"
  have norm: "lp_cut_normalize fuel eqs (map (\<lambda>x. LPCAtom (Var x)) vs) =
      Some (Some (map LPCAtom ts))"
    using checked by (simp add: lp_cut_check_interface_def)
  have same: "\<And>x. lp_ieval (?mu x) \<eta> = \<eta> x"
    by (rule lp_cut_normalized_interface_valuation[OF equations norm])
  have interpreted: "\<forall>x\<in>set G. lp_seg_ground (lp_ieval (?mu x) \<eta>)"
    using knowledge by (simp add: same knowledge_def)
  have variables: "\<forall>x\<in>set G. \<forall>y\<in>vars_term (?mu x). lp_seg_ground (\<eta> y)"
    using interpreted by (simp add: lp_seg_ground_eval)
  have ground: "\<forall>x\<in>set H. lp_seg_ground (\<eta> x)"
    using checked variables by (auto simp: lp_cut_check_interface_def)
  have guards: "\<And>g. g\<in>set guards' \<Longrightarrow> guard_holds g \<eta>"
  proof -
    fix g assume member: "g\<in>set guards'"
    obtain h where h: "h\<in>set guards" and g: "g=lp_cut_guard_subst ?mu h"
      using checked member by (auto simp: lp_cut_check_interface_def)
    have "guard_holds h \<eta>"
      using knowledge h by (auto simp: knowledge_def list_all_iff)
    then show "guard_holds g \<eta>"
      by (simp add: g guard_subst same)
  qed
  show ?thesis using ground guards knowledge by (auto simp: knowledge_def list_all_iff)
qed

end
end
