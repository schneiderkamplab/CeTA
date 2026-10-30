theory LP_Prolog_Arithmetic
  imports LP_Prolog_Integer_NO
begin

text \<open>Integer expression evidence is bound to the original source term.
A variable is not interpreted numerically merely because it is ground.
Constant-divisor operators use Prolog's floor quotient and signed remainder;
zero divisors are excluded from successful evaluation evidence.\<close>

datatype 'v lpp_integer_expression =
    LPPEConstant int | LPPEVariable 'v
  | LPPEPositive "'v lpp_integer_expression"
  | LPPENegate "'v lpp_integer_expression"
  | LPPEAdd "'v lpp_integer_expression" "'v lpp_integer_expression"
  | LPPESubtract "'v lpp_integer_expression" "'v lpp_integer_expression"
  | LPPEMultiply "'v lpp_integer_expression" "'v lpp_integer_expression"
  | LPPEDivide "'v lpp_integer_expression" int
  | LPPEModulo "'v lpp_integer_expression" int

fun lpp_expression_term where
  "lpp_expression_term (LPPEConstant n) = lpp_integer_term n"
| "lpp_expression_term (LPPEVariable x) = Var x"
| "lpp_expression_term (LPPEPositive a) = Fun (LPCUser ''1:prolog_data_2b'') [lpp_expression_term a]"
| "lpp_expression_term (LPPENegate a) = Fun (LPCUser ''1:prolog_data_2d'') [lpp_expression_term a]"
| "lpp_expression_term (LPPEAdd a b) = Fun (LPCUser ''2:prolog_data_2b'') [lpp_expression_term a,lpp_expression_term b]"
| "lpp_expression_term (LPPESubtract a b) = Fun (LPCUser ''2:prolog_data_2d'') [lpp_expression_term a,lpp_expression_term b]"
| "lpp_expression_term (LPPEMultiply a b) = Fun (LPCUser ''2:prolog_data_2a'') [lpp_expression_term a,lpp_expression_term b]"
| "lpp_expression_term (LPPEDivide a d) = Fun (LPCUser ''2:prolog_data_646976'') [lpp_expression_term a,lpp_integer_term d]"
| "lpp_expression_term (LPPEModulo a d) = Fun (LPCUser ''2:prolog_data_6d6f64'') [lpp_expression_term a,lpp_integer_term d]"

fun lpp_expression_value where
  "lpp_expression_value (LPPEConstant n) rho = n"
| "lpp_expression_value (LPPEVariable x) rho = rho x"
| "lpp_expression_value (LPPEPositive a) rho = lpp_expression_value a rho"
| "lpp_expression_value (LPPENegate a) rho = - lpp_expression_value a rho"
| "lpp_expression_value (LPPEAdd a b) rho = lpp_expression_value a rho + lpp_expression_value b rho"
| "lpp_expression_value (LPPESubtract a b) rho = lpp_expression_value a rho - lpp_expression_value b rho"
| "lpp_expression_value (LPPEMultiply a b) rho = lpp_expression_value a rho * lpp_expression_value b rho"
| "lpp_expression_value (LPPEDivide a d) rho = lpp_expression_value a rho div d"
| "lpp_expression_value (LPPEModulo a d) rho = lpp_expression_value a rho mod d"

fun lpp_expression_check where
  "lpp_expression_check K (LPPEConstant n) = True"
| "lpp_expression_check K (LPPEVariable x) = (x\<in>set K)"
| "lpp_expression_check K (LPPEPositive a) = lpp_expression_check K a"
| "lpp_expression_check K (LPPENegate a) = lpp_expression_check K a"
| "lpp_expression_check K (LPPEAdd a b) = (lpp_expression_check K a \<and> lpp_expression_check K b)"
| "lpp_expression_check K (LPPESubtract a b) = (lpp_expression_check K a \<and> lpp_expression_check K b)"
| "lpp_expression_check K (LPPEMultiply a b) = (lpp_expression_check K a \<and> lpp_expression_check K b)"
| "lpp_expression_check K (LPPEDivide a d) = (lpp_expression_check K a \<and> d\<noteq>0)"
| "lpp_expression_check K (LPPEModulo a d) = (lpp_expression_check K a \<and> d\<noteq>0)"

inductive lpp_integer_evaluation :: "(string lp_cut_symbol,'w) lp_iterm \<Rightarrow> int \<Rightarrow> bool" where
  literal: "lpp_integer_evaluation (lpp_integer_value n) n"
| positive: "lpp_integer_evaluation a n \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''1:prolog_data_2b'') [a]) n"
| negate: "lpp_integer_evaluation a n \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''1:prolog_data_2d'') [a]) (-n)"
| add: "lpp_integer_evaluation a n \<Longrightarrow> lpp_integer_evaluation b m \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_2b'') [a,b]) (n+m)"
| subtract: "lpp_integer_evaluation a n \<Longrightarrow> lpp_integer_evaluation b m \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_2d'') [a,b]) (n-m)"
| multiply: "lpp_integer_evaluation a n \<Longrightarrow> lpp_integer_evaluation b m \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_2a'') [a,b]) (n*m)"
| divide: "lpp_integer_evaluation a n \<Longrightarrow> d\<noteq>0 \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_646976'') [a,lpp_integer_value d]) (n div d)"
| modulo: "lpp_integer_evaluation a n \<Longrightarrow> d\<noteq>0 \<Longrightarrow>
    lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,lpp_integer_value d]) (n mod d)"

lemma lpp_integer_literal_eval[simp]:
  "lp_ieval (lpp_integer_term n) eta = lpp_integer_value n"
  by (simp add: lpp_integer_term_def lpp_integer_value_def)

theorem lpp_expression_evaluation:
  assumes checked: "lpp_expression_check K e"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) eta) (lpp_expression_value e rho)"
  using checked
  by (induct e) (auto intro: lpp_integer_evaluation.intros simp: typed)

definition lpp_integer_known where
  "lpp_integer_known K eta = (\<forall>x\<in>set K. \<exists>n. eta x=lpp_integer_value n)"

lemma lpp_integer_known_environment:
  assumes "lpp_integer_known K eta"
  shows "\<exists>rho. \<forall>x\<in>set K. eta x=lpp_integer_value (rho x)"
proof -
  have "\<forall>x. \<exists>n. x\<in>set K \<longrightarrow> eta x=lpp_integer_value n"
    using assms by (auto simp: lpp_integer_known_def)
  then show ?thesis by metis
qed

corollary lpp_checked_expression_finishes:
  "lpp_expression_check K e \<Longrightarrow> lpp_integer_known K eta \<Longrightarrow>
   \<exists>n. lpp_integer_evaluation (lp_ieval (lpp_expression_term e) eta) n"
  using lpp_integer_known_environment lpp_expression_evaluation by blast


lemma lpp_integer_value_subst[simp]:
  "lp_isubst (lpp_integer_value n) sigma = lpp_integer_value n"
  by (simp add: lpp_integer_value_def)

lemma lpp_integer_evaluation_subst:
  "lpp_integer_evaluation a n \<Longrightarrow> lp_isubst a sigma=a"
  by (induction rule: lpp_integer_evaluation.induct) simp_all

lemma lpp_integer_known_subst:
  "lpp_integer_known K eta \<Longrightarrow> lpp_integer_known K (\<lambda>x. lp_isubst (eta x) sigma)"
  by (unfold lpp_integer_known_def) (metis lpp_integer_value_subst)

end
