theory TRS_Conditional_Examples
  imports TRS_Conditional_Operational_Properties TRS_Standard_Examples
begin
lemma empty_conditional_success:
  assumes "conditional_success A {} g"
  shows "case g of CRewrite s t \<Rightarrow> False | CReach s t \<Rightarrow> s=t"
  using assms by (induct rule: conditional_success.induct)
    (erule conditional_inference.cases; auto)
lemma empty_ordinary_terminates: "trs_conditional_terminates A {}"
  using empty_conditional_success[of A "CRewrite _ _"]
  by (auto simp: trs_conditional_terminates_def no_infinite_steps_def conditional_step_def)

text \<open>The circular condition a reaches b never succeeds. Thus there are
no completed rewrites, although evaluation can repeatedly call itself.\<close>
abbreviation ca :: "(bool,nat) fo_term" where "ca \<equiv> SFun False []"
abbreviation cb :: "(bool,nat) fo_term" where "cb \<equiv> SFun True []"
definition circular_rules where "circular_rules = {((ca,cb),[(ca,cb)])}"
definition constants :: "bool ranked_signature" where "constants f = Some 0"
lemma circular_success:
  assumes "conditional_success constants circular_rules g"
  shows "case g of CRewrite s t \<Rightarrow> False | CReach s t \<Rightarrow> s=t"
  using assms by (induct rule: conditional_success.induct)
    (erule conditional_inference.cases; auto simp: circular_rules_def)
lemma circular_ordinary_terminates:
  "trs_conditional_terminates constants circular_rules"
  using circular_success[of "CRewrite _ _"]
  by (auto simp: trs_conditional_terminates_def no_infinite_steps_def conditional_step_def)
lemma circular_call:
  "conditional_evaluation_step constants circular_rules (CRewrite ca cb) (CReach ca cb)"
proof -
  have inf: "conditional_inference constants circular_rules (CRewrite ca cb) [CReach ca cb]"
    using conditional_inference.rule[of ca cb "[(ca,cb)]" circular_rules constants SHole SVar]
    by (simp add: circular_rules_def constants_def correct_substitution_def)
  show ?thesis unfolding conditional_evaluation_step_def
    by (intro exI[of _ "[CReach ca cb]"] exI[of _ 0]) (simp add: inf)
qed
lemma circular_reach:
  "conditional_evaluation_step constants circular_rules (CReach ca cb) (CRewrite ca cb)"
  unfolding conditional_evaluation_step_def
  by (intro exI[of _ "[CRewrite ca cb, CReach cb cb]"] exI[of _ 0] conjI;
    (rule conditional_inference.transitive; simp add: constants_def | simp add: constants_def))
lemma circular_operational_nontermination:
  "\<not> trs_conditional_operationally_terminates constants circular_rules"
  unfolding trs_conditional_operational_nontermination_iff
  by (intro exI[of _ "\<lambda>i. if even i then CReach ca cb else CRewrite ca cb"] allI)
    (simp add: circular_call circular_reach)
lemma circular_valid: "conditional_problem constants circular_rules"
  by (simp add: conditional_problem_def circular_rules_def constants_def)

lemma unconditional_step_iff:
  "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t \<longleftrightarrow> fo_step A R s t"
proof
  assume "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t"
  then obtain gs where "conditional_inference A ((\<lambda>(l,r). ((l,r),[])) ` R) (CRewrite s t) gs"
    unfolding conditional_step_def by (cases rule: conditional_success.cases) auto
  then show "fo_step A R s t"
    by (cases rule: conditional_inference.cases) (auto simp: fo_step_def)
next
  assume "fo_step A R s t"
  then obtain l r C sigma where lr: "(l,r) \<in> R"
    and wf: "arity_correct A s" "arity_correct A t" "correct_context A C"
      "correct_substitution A sigma"
    and eq: "s = fo_plug C (fo_subst sigma l)"
      "t = fo_plug C (fo_subst sigma r)"
    by (auto simp: fo_step_def)
  have inf: "conditional_inference A ((\<lambda>(l,r). ((l,r),[])) ` R) (CRewrite s t) []"
    using conditional_inference.rule[of l r "[]" "(\<lambda>(l,r). ((l,r),[])) ` R" A C sigma] wf lr
    by (auto simp: eq)
  show "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t"
    unfolding conditional_step_def by (rule conditional_success.derive[OF inf]) simp
qed
lemma unconditional_ordinary_iff:
  "trs_conditional_terminates A ((\<lambda>(l,r). ((l,r),[])) ` R) \<longleftrightarrow> trs_standard_terminates A R"
  by (simp only: trs_conditional_terminates_def trs_standard_terminates_def no_infinite_steps_def
      no_infinite_steps_def unconditional_step_iff)
lemma unary_conditional_loop:
  "\<not> trs_conditional_terminates unary
    {((SFun () [SVar (0::nat)],SFun () [SVar (0::nat)]),[])}"
  using unconditional_ordinary_iff[of unary "{(SFun () [SVar (0::nat)],SFun () [SVar (0::nat)])}"]
    no_constants_nontermination by simp
lemma arity_mismatch_not_a_conditional_step:
  "\<not> conditional_step unary R (SFun () []) t"
  using conditional_step_correct[of unary R "SFun () []" t] by (auto simp: unary_def)

text \<open>A genuine condition can succeed without taking a step. The rewrite
then occurs below the root with a nonground substitution, over the shared unary
signature with no constants.\<close>
abbreviation guarded_reduction :: "(unit,nat) conditional_rule set" where
  "guarded_reduction \<equiv> {((SFun () [SVar 0],SVar 0),[(SVar 0,SVar 0)])}"
lemma conditional_below_root_nonground:
  "conditional_step unary guarded_reduction
    (SFun () [SFun () [SVar 7]]) (SFun () [SVar 7])"
proof -
  have success: "conditional_success unary guarded_reduction (CReach (SVar 7) (SVar 7))"
    by (rule conditional_success.derive[where gs="[]"];
      (rule conditional_inference.reflexive; simp | simp))
  have inf: "conditional_inference unary guarded_reduction
    (CRewrite (SFun () [SFun () [SVar 7]]) (SFun () [SVar 7])) [CReach (SVar 7) (SVar 7)]"
    using conditional_inference.rule[of "SFun () [SVar 0]" "SVar 0"
      "[(SVar 0,SVar 0)]" guarded_reduction unary "SMore () [] SHole []" "\<lambda>_. SVar 7"]
    by (simp add: unary_def correct_substitution_def)
  show ?thesis unfolding conditional_step_def
    by (rule conditional_success.derive[OF inf]) (simp add: success)
qed
lemma conditional_step_implies_erased_step:
  assumes "conditional_step A R s t"
  shows "fo_step A (fst ` R) s t"
proof -
  obtain gs where "conditional_inference A R (CRewrite s t) gs"
    using assms unfolding conditional_step_def by (cases rule: conditional_success.cases) auto
  then obtain l r cs C sigma where lr: "((l,r),cs) \<in> R"
    and ctxt: "correct_context A C" and sub: "correct_substitution A sigma"
    and wf: "arity_correct A s" "arity_correct A t"
    and eq: "s=fo_plug C (fo_subst sigma l)"
      "t=fo_plug C (fo_subst sigma r)"
    by (cases rule: conditional_inference.cases) auto
  have member: "(l,r) \<in> fst ` R" using imageI[OF lr, of fst] by simp
  show ?thesis unfolding fo_step_def using member ctxt sub wf eq by blast
qed
lemma conditional_reduction_terminates:
  "trs_conditional_terminates unary guarded_reduction"
proof -
  have transfer: "conditional_step unary guarded_reduction s t \<Longrightarrow>
      fo_step unary {(SFun () [SVar (0::nat)],SVar 0)} s t" for s t
    using conditional_step_implies_erased_step[of unary guarded_reduction s t] by simp
  show ?thesis using reduction_terminates[of unary "()"] transfer
    unfolding trs_conditional_terminates_def trs_standard_terminates_def no_infinite_steps_def no_infinite_steps_def by blast
qed

lemma empty_evaluation_shape:
  assumes "conditional_evaluation_step A {} g h"
  shows "\<exists>s t u. g=CReach s t \<and> h=CRewrite s u"
proof -
  obtain gs i where inf: "conditional_inference A {} g gs" and idx: "i < length gs"
    and pre: "\<And>j. j<i \<Longrightarrow> conditional_success A {} (gs!j)" and h: "h=gs!i"
    using assms by (auto simp: conditional_evaluation_step_def)
  from inf show ?thesis
  proof cases
    case (reflexive s)
    with idx show ?thesis by simp
  next
    case (transitive s u t)
    have cases: "i=0 \<or> i=1" using idx transitive by auto
    have "i \<noteq> 1"
    proof
      assume "i=1"
      then have "conditional_success A {} (CRewrite s u)" using pre[of 0] transitive by simp
      from empty_conditional_success[OF this] show False by simp
    qed
    with cases transitive h show ?thesis by auto
  next
    case (rule l r cs C sigma)
    then show ?thesis by simp
  qed
qed
lemma empty_operational_terminates:
  "trs_conditional_operationally_terminates A ({} :: ('f,'v) conditional_rule set)"
proof (rule ccontr)
  assume "\<not> trs_conditional_operationally_terminates A ({} :: ('f,'v) conditional_rule set)"
  then obtain gs :: "nat \<Rightarrow> ('f,'v) conditional_goal" where steps: "\<And>i. conditional_evaluation_step A {} (gs i) (gs (Suc i))"
    by (auto simp: trs_conditional_operational_nontermination_iff)
  from empty_evaluation_shape[OF steps[of 0]] empty_evaluation_shape[OF steps[of 1]]
  show False by auto
qed
end
