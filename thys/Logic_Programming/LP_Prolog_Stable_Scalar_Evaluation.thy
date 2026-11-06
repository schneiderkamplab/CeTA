theory LP_Prolog_Stable_Scalar_Evaluation
  imports LP_Prolog_Scalar_Bound_Controls
begin

text \<open>A successful arithmetic observation evaluates operands with one
fixed partial operation table. This extends scalar observations to compound
expressions without specifying a new Prolog execution relation. The operation
table is a parameter, not a certificate witness. A source bridge must establish
its integer-operation contract and cover failure/error outcomes separately.
In particular, no result is inferred solely from termination or groundness.\<close>

lemma lpp_scalar_fraction_nullary:
  "lpp_scalar_fraction t n d \<Longrightarrow> \<exists>f. t=LPIFun (LPCUser f) []"
  by (auto simp: lpp_scalar_fraction_def lpp_integer_value_def lpp_binary64_value_def)

inductive lpp_stable_scalar_evaluation where
  scalar: "lpp_scalar_fraction t n d \<Longrightarrow> lpp_stable_scalar_evaluation operation t t"
| unary: "lpp_stable_scalar_evaluation operation a x \<Longrightarrow>
    operation f [x]=Some v \<Longrightarrow> lpp_scalar_fraction v n d \<Longrightarrow>
    lpp_stable_scalar_evaluation operation (LPIFun f [a]) v"
| binary: "lpp_stable_scalar_evaluation operation a x \<Longrightarrow>
    lpp_stable_scalar_evaluation operation b y \<Longrightarrow>
    operation f [x,y]=Some v \<Longrightarrow> lpp_scalar_fraction v n d \<Longrightarrow>
    lpp_stable_scalar_evaluation operation (LPIFun f [a,b]) v"

lemma lpp_stable_scalar_evaluation_unique:
  assumes first: "lpp_stable_scalar_evaluation operation expression v"
    and second: "lpp_stable_scalar_evaluation operation expression w"
  shows "v=w"
  using first second
proof (induction arbitrary: w rule: lpp_stable_scalar_evaluation.induct)
  case (scalar t n d operation)
  from scalar.prems show ?case
    by (cases rule: lpp_stable_scalar_evaluation.cases)
      (use scalar.hyps in \<open>auto dest: lpp_scalar_fraction_nullary\<close>)
next
  case (unary operation a x f v n d)
  from unary.prems obtain z where evaluated: "lpp_stable_scalar_evaluation operation a z"
    and returned: "operation f [z]=Some w"
    by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have "x=z" by (rule unary.IH[OF evaluated])
  then show ?case using unary.hyps returned by simp
next
  case (binary operation a x b y f v n d)
  from binary.prems obtain z q where left: "lpp_stable_scalar_evaluation operation a z"
    and right: "lpp_stable_scalar_evaluation operation b q"
    and returned: "operation f [z,q]=Some w"
    by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have "x=z" by (rule binary.IH(1)[OF left])
  moreover have "y=q" by (rule binary.IH(2)[OF right])
  ultimately show ?case using binary.hyps returned by simp
qed

lemma lpp_stable_scalar_evaluation_result:
  "lpp_stable_scalar_evaluation operation expression v \<Longrightarrow>
    \<exists>n d. lpp_scalar_fraction v n d"
  by (erule lpp_stable_scalar_evaluation.cases) auto

lemma lpp_stable_scalar_evaluation_ground:
  "lpp_stable_scalar_evaluation operation expression v \<Longrightarrow>
    lp_seg_ground expression \<and> lp_seg_ground v"
  by (induction rule: lpp_stable_scalar_evaluation.induct)
    (auto dest: lpp_scalar_fraction_ground intro: lp_seg_ground.intros)

lemma lpp_stable_scalar_evaluation_subst:
  assumes evaluated: "lpp_stable_scalar_evaluation operation expression v"
  shows "lpp_stable_scalar_evaluation operation (lp_isubst expression sigma) (lp_isubst v sigma)"
  using evaluated lpp_stable_scalar_evaluation_ground[OF evaluated]
  by (simp add: lp_seg_ground_subst)

lemma lpp_stable_evaluated_bound:
  assumes first: "lpp_stable_scalar_evaluation operation expression v"
    and second: "lpp_stable_scalar_evaluation operation (lp_isubst expression sigma) w"
  shows "lpp_scalar_floor v=lpp_scalar_floor w"
proof -
  have fixed: "lp_isubst expression sigma=expression"
    using lpp_stable_scalar_evaluation_ground[OF first] by (simp add: lp_seg_ground_subst)
  have "v=w" by (rule lpp_stable_scalar_evaluation_unique[OF first]) (use second fixed in simp)
  then show ?thesis by simp
qed

ML \<open>
val checked = [@{thm lpp_stable_scalar_evaluation_unique},
  @{thm lpp_stable_scalar_evaluation_result}, @{thm lpp_stable_scalar_evaluation_ground},
  @{thm lpp_stable_scalar_evaluation_subst}, @{thm lpp_stable_evaluated_bound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable scalar evaluation dependency" else ();
\<close>
end
