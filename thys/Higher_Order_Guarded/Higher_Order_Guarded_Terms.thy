theory Higher_Order_Guarded_Terms
  imports "Higher_Order_Prefix.Higher_Order_Prefix_Schema"
begin

text \<open>A closed family of algebraic, variable-preserving rules retains
dependence on a surrounding binder. This excludes matching a constant
abstraction without assuming that its body is already a normal form.\<close>

fun ho_guard_body where
  "ho_guard_body F (HBound n)=True"
| "ho_guard_body F (HConst c)=(c\<in>F)"
| "ho_guard_body F (HApp t u)=(ho_guard_body F t \<and> ho_guard_body F u)"
| "ho_guard_body F t=False"

fun ho_guard_template where
  "ho_guard_template F (HFree n)=True"
| "ho_guard_template F (HConst c)=(c\<in>F)"
| "ho_guard_template F (HApp t u)=(ho_guard_template F t \<and> ho_guard_template F u)"
| "ho_guard_template F t=False"

fun ho_guard_vars where
  "ho_guard_vars (HFree n)={n}"
| "ho_guard_vars (HApp t u)=ho_guard_vars t \<union> ho_guard_vars u"
| "ho_guard_vars t={}"

fun ho_guard_occurs where
  "ho_guard_occurs n (HBound m)=(n=m)"
| "ho_guard_occurs n (HApp t u)=(ho_guard_occurs n t \<or> ho_guard_occurs n u)"
| "ho_guard_occurs n t=False"

lemma guard_subst_body:
  assumes template: "ho_guard_template F t"
  shows "ho_guard_body F (ho_subst s 0 t) =
    (\<forall>n\<in>ho_guard_vars t. ho_guard_body F (s n))"
  using template by (induction t) auto

lemma guard_subst_occurs:
  assumes template: "ho_guard_template F t"
  shows "ho_guard_occurs k (ho_subst s 0 t) =
    (\<exists>n\<in>ho_guard_vars t. ho_guard_occurs k (s n))"
  using template by (induction t) auto

lemma guard_subst_preserves:
  assumes left: "ho_guard_template F l"
    and right: "ho_guard_template F r"
    and vars: "ho_guard_vars l=ho_guard_vars r"
    and body: "ho_guard_body F (ho_subst s 0 l)"
  shows "ho_guard_body F (ho_subst s 0 r)"
    "ho_guard_occurs k (ho_subst s 0 r)=ho_guard_occurs k (ho_subst s 0 l)"
  using guard_subst_body[OF left, of s] guard_subst_body[OF right, of s]
    guard_subst_occurs[OF left, of k s] guard_subst_occurs[OF right, of k s]
    vars body by auto

definition ho_guard_rules where
  "ho_guard_rules F R = list_all (\<lambda>(G,l,r).
    case ho_application_head (ho_erase_pattern l) of HConst c \<Rightarrow>
      (if c\<in>F then ho_guard_template F (ho_erase_pattern l) \<and>
         ho_guard_template F (ho_erase_pattern r) \<and>
         ho_guard_vars (ho_erase_pattern l)=ho_guard_vars (ho_erase_pattern r)
       else True)
    | _ \<Rightarrow> False) R"

fun ho_guard_lambda where
  "ho_guard_lambda F (HAbs A t)=(ho_guard_body F t \<and> ho_guard_occurs 0 t)"
| "ho_guard_lambda F t=False"

fun ho_constant_abstraction where
  "ho_constant_abstraction (HAbs A (HFree n))=True"
| "ho_constant_abstraction t=False"

definition ho_guard_clash where
  "ho_guard_clash F xs ls = (\<exists>i<length xs. i<length ls \<and>
    ho_guard_lambda F (xs!i) \<and> ho_constant_abstraction (ls!i))"

definition ho_guard_blocked where
  "ho_guard_blocked F R c xs = list_all (\<lambda>(G,l,r).
    ho_application_head (ho_erase_pattern l)\<noteq>HConst c \<or>
    ho_guard_clash F xs (ho_spine_arguments (ho_erase_pattern l))) R"

lemma ho_guard_clash_code [code]:
  "ho_guard_clash F xs ls = list_ex (\<lambda>i. i<length ls \<and>
    ho_guard_lambda F (xs!i) \<and> ho_constant_abstraction (ls!i)) [0..<length xs]"
  by (auto simp: ho_guard_clash_def list_ex_iff)

lemma guard_lift_no_new_bound:
  "k<d \<Longrightarrow> \<not>ho_guard_occurs k (ho_lift d 0 t)"
  by (induction t) auto

lemma guard_constant_abstraction_subst:
  assumes "ho_constant_abstraction t"
  shows "\<not>ho_guard_lambda F (ho_subst s 0 t)"
proof -
  obtain A n where t: "t=HAbs A (HFree n)"
    using assms by (cases t rule: ho_constant_abstraction.cases) auto
  show ?thesis by (simp add: t guard_lift_no_new_bound)
qed

lemma guard_body_open:
  "ho_guard_body F t \<Longrightarrow> ho_bound_closed k t \<Longrightarrow> ho_open s b k t=t"
  by (induction t) auto

lemma guard_lambda_open:
  "ho_guard_lambda F t \<Longrightarrow> ho_bound_closed 0 t \<Longrightarrow> ho_open s b 0 t=t"
  by (cases t) (auto simp: guard_body_open)

lemma guard_body_head:
  "ho_guard_body F t \<Longrightarrow> ho_application_head t=HConst c \<Longrightarrow> c\<in>F"
  by (induction t) auto

context ho_source_neutral_reducibility
begin

lemma guard_source_step:
  assumes rules: "ho_guard_rules F R"
    and step: "ho_step S V R C t u"
    and body: "ho_guard_body F t"
  shows "ho_guard_body F u \<and> ho_guard_occurs k u=ho_guard_occurs k t"
  using step body
proof (induction rule: ho_step.induct)
  case (rule G l r B s t u)
  obtain c where head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using constant_heads rule.hyps(1) by blast
  have h: "ho_application_head t=HConst c"
    using rule_instance_head_spine(1)[OF rule.hyps(1,4)] head by simp
  have cf: "c\<in>F" by (rule guard_body_head[OF rule.prems h])
  have lt: "ho_guard_template F (ho_erase_pattern l)"
    and rt: "ho_guard_template F (ho_erase_pattern r)"
    and vars: "ho_guard_vars (ho_erase_pattern l)=ho_guard_vars (ho_erase_pattern r)"
    using rules rule.hyps(1) cf head by (auto simp: ho_guard_rules_def list_all_iff)
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero rule.hyps(1) by (auto simp: ho_zero_arity_rules_def)
  have tl: "t=ho_subst s 0 (ho_erase_pattern l)"
    using rule.hyps(4) ho_zero_arity_instantiate[OF zl, of s 0] by simp
  have ur: "u=ho_subst s 0 (ho_erase_pattern r)"
    using rule.hyps(5) ho_zero_arity_instantiate[OF zr, of s 0] by simp
  show ?case using guard_subst_preserves[OF lt rt vars, of s] rule.prems
    by (simp add: tl ur)
qed auto

lemma guard_abstraction_step:
  assumes rules: "ho_guard_rules F R"
    and step: "ho_step S V R B (HAbs A t) u"
    and body: "ho_guard_body F t"
  obtains v where "u=HAbs A v" "ho_guard_body F v"
    "ho_guard_occurs k v=ho_guard_occurs k t"
  using step
proof (cases rule: ho_step.cases)
  case (rule G l r s)
  have "\<exists>c. ho_application_head (HAbs A t)=HConst c"
    using rule_instance_constant_head[OF rule(1,4)] by blast
  then show thesis by simp
next
  case (abs v)
  show thesis using guard_source_step[OF rules abs(2) body, of k] abs(1) that by blast
qed

lemma guard_lambda_step:
  assumes rules: "ho_guard_rules F R"
    and step: "ho_step S V R B t u"
    and body: "ho_guard_lambda F t"
  shows "ho_guard_lambda F u"
proof -
  obtain A v where t: "t=HAbs A v" and vb: "ho_guard_body F v"
    and occ: "ho_guard_occurs 0 v"
    using body by (cases t) auto
  have st: "ho_step S V R B (HAbs A v) u" using step t by simp
  obtain w where uw: "u=HAbs A w" and wb: "ho_guard_body F w"
    and wo: "ho_guard_occurs 0 w=ho_guard_occurs 0 v"
    by (rule guard_abstraction_step[where k=0, OF rules st vb])
  show ?thesis using uw wb wo occ by simp
qed

end
end
