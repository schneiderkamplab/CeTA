theory TRS_Conditional_Examples
  imports TRS_Conditional_Operational_Spec TRS_Standard_Examples
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
abbreviation ca :: "(bool,nat) standard_term" where "ca \<equiv> SFun False []"
abbreviation cb :: "(bool,nat) standard_term" where "cb \<equiv> SFun True []"
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
  "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t \<longleftrightarrow> standard_step A R s t"
proof
  assume "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t"
  then obtain gs where "conditional_inference A ((\<lambda>(l,r). ((l,r),[])) ` R) (CRewrite s t) gs"
    unfolding conditional_step_def by (cases rule: conditional_success.cases) auto
  then show "standard_step A R s t"
    by (cases rule: conditional_inference.cases) (auto simp: standard_step_def)
next
  assume "standard_step A R s t"
  then obtain l r C sigma where lr: "(l,r) \<in> R"
    and wf: "arity_correct A s" "arity_correct A t" "correct_context A C"
      "correct_substitution A sigma"
    and eq: "s = standard_plug C (standard_subst sigma l)"
      "t = standard_plug C (standard_subst sigma r)"
    by (auto simp: standard_step_def)
  have inf: "conditional_inference A ((\<lambda>(l,r). ((l,r),[])) ` R) (CRewrite s t) []"
    using conditional_inference.rule[of l r "[]" "(\<lambda>(l,r). ((l,r),[])) ` R" A C sigma] wf lr
    by (auto simp: eq)
  show "conditional_step A ((\<lambda>(l,r). ((l,r),[])) ` R) s t"
    unfolding conditional_step_def by (rule conditional_success.derive[OF inf]) simp
qed
lemma unconditional_ordinary_iff:
  "trs_conditional_terminates A ((\<lambda>(l,r). ((l,r),[])) ` R) \<longleftrightarrow> trs_standard_terminates A R"
  by (simp only: trs_conditional_terminates_def trs_standard_terminates_def
      no_infinite_steps_def unconditional_step_iff)
lemma unary_conditional_loop:
  "\<not> trs_conditional_terminates unary
    {((SFun () [SVar (0::nat)],SFun () [SVar (0::nat)]),[])}"
  using unconditional_ordinary_iff[of unary "{(SFun () [SVar (0::nat)],SFun () [SVar (0::nat)])}"]
    no_constants_nontermination by simp
lemma arity_mismatch_not_a_conditional_step:
  "\<not> conditional_step unary R (SFun () []) t"
  using conditional_step_correct[of unary R "SFun () []" t] by (auto simp: unary_def)
end
