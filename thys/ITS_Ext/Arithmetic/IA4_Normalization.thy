theory IA4_Normalization
  imports IA_Div_Mod
begin

type_synonym 'v ia4_exp = "(ia4_sig,'v,IA.ty) Sorted_Algebra.exp"
datatype 'v ia4_variable = IA4_Old 'v | IA4_Quot "'v ia4_exp" | IA4_Rem "'v ia4_exp"
derive compare_order ia4_variable

instantiation ia4_variable :: (showl) showl
begin
fun showsl_ia4_variable where
 "showsl_ia4_variable (IA4_Old x) = showsl x"
| "showsl_ia4_variable (IA4_Quot e) = showsl_lit (STR ''quotient('') o showsl e o showsl_lit (STR '')'')"
| "showsl_ia4_variable (IA4_Rem e) = showsl_lit (STR ''remainder('') o showsl e o showsl_lit (STR '')'')"
definition "showsl_list (xs :: 'a ia4_variable list) = default_showsl_list showsl xs"
instance ..
end


definition divisor_value where
  "divisor_value e = IA.to_int (IA4.eval e (\<lambda>_. IA.Int 0))"

fun supported_exp :: "'v ia4_exp \<Rightarrow> bool" where
  "supported_exp (Var _) = True"
| "supported_exp (Fun (IA4_Base _) es) = list_all supported_exp es"
| "supported_exp (Fun IA4_Div [a,d]) =
    (supported_exp a \<and> supported_exp d \<and> vars_term d = {} \<and> divisor_value d \<noteq> 0)"
| "supported_exp (Fun IA4_Mod [a,d]) =
    (supported_exp a \<and> supported_exp d \<and> vars_term d = {} \<and> divisor_value d \<noteq> 0)"
| "supported_exp _ = False"

fun lower_exp :: "'v ia4_exp \<Rightarrow> 'v ia4_variable IA.exp" where
  "lower_exp (Var (v,ty)) = Var (IA4_Old v,ty)"
| "lower_exp (Fun (IA4_Base f) es) = Fun f (map lower_exp es)"
| "lower_exp (Fun IA4_Div [a,d]) = IA.var (IA4_Quot (Fun IA4_Div [a,d]))"
| "lower_exp (Fun IA4_Mod [a,d]) = IA.var (IA4_Rem (Fun IA4_Div [a,d]))"
| "lower_exp _ = IA.const 0"

fun quotient_value where
  "quotient_value alpha (Fun _ [a,d]) = euclid_quot (IA.to_int (IA4.eval a alpha)) (IA.to_int (IA4.eval d alpha))"
| "quotient_value alpha _ = 0"
fun remainder_value where
  "remainder_value alpha (Fun _ [a,d]) = euclid_rem (IA.to_int (IA4.eval a alpha)) (IA.to_int (IA4.eval d alpha))"
| "remainder_value alpha _ = 0"
fun lifted_valuation where
  "lifted_valuation alpha (IA4_Old x,ty) = alpha (x,ty)"
| "lifted_valuation alpha (IA4_Quot e,IA.IntT) = IA.Int (quotient_value alpha e)"
| "lifted_valuation alpha (IA4_Rem e,IA.IntT) = IA.Int (remainder_value alpha e)"
| "lifted_valuation alpha (_,IA.BoolT) = IA.Bool False"

lemma lifted_assignment:
  assumes ass: "IA4.assignment alpha"
  shows "IA.assignment (lifted_valuation alpha)"
proof (rule IA.assignmentI)
  fix x ty
  show "lifted_valuation alpha (x,ty) \<in> IA.Values_of_type ty"
  proof (cases x)
    case (IA4_Old y)
    with IA4.assignmentD[OF ass, of "(y,ty)"] show ?thesis by simp
  qed (cases ty; auto)+
qed

lemma lower_exp_type:
  "IA4.has_type e ty \<Longrightarrow> IA.has_type (lower_exp e) ty"
proof (induct e arbitrary: ty)
  case (Var x) then show ?case by (cases x, auto)
next
  case (Fun f es)
  show ?case
  proof (cases f)
    case (IA4_Base g)
    with Fun show ?thesis by (auto simp: set_conv_nth; blast)
  next
    case IA4_Div
    with Fun show ?thesis by (cases es rule: list_3_cases, auto)
  next
    case IA4_Mod
    with Fun show ?thesis by (cases es rule: list_3_cases, auto)
  qed
qed

lemma lower_exp_eval:
  "IA4.has_type e ty \<Longrightarrow> IA.eval (lower_exp e) (lifted_valuation alpha) = IA4.eval e alpha"
proof (induct e arbitrary: ty)
  case (Var x) then show ?case by (cases x, auto)
next
  case (Fun f es)
  show ?case
  proof (cases f)
    case (IA4_Base g)
    have maps: "map (\<lambda>e. IA.eval (lower_exp e) (lifted_valuation alpha)) es = map (\<lambda>e. IA4.eval e alpha) es"
      by (rule map_cong[OF refl], insert Fun IA4_Base, auto simp: set_conv_nth; blast)
    show ?thesis by (simp only: IA4_Base algebra.eval.simps lower_exp.simps IA4.I.simps map_map o_def maps)
  next
    case IA4_Div
    with Fun.prems obtain a d where "es = [a,d]" by (cases es rule: list_3_cases, auto)
    with IA4_Div show ?thesis by simp
  next
    case IA4_Mod
    with Fun.prems obtain a d where "es = [a,d]" by (cases es rule: list_3_cases, auto)
    with IA4_Mod show ?thesis by simp
  qed
qed

lemma constant_eval:
  "vars_term e = {} \<Longrightarrow> IA4.eval e alpha = IA4.eval e beta"
  by (rule IA4.eval_same_vars, simp)

abbreviation qvar where "qvar e \<equiv> IA.var (IA4_Quot e)"
abbreviation rvar where "rvar e \<equiv> IA.var (IA4_Rem e)"

definition qr_constraints where
  "qr_constraints e a d = [
    lower_exp a =\<^sub>I\<^sub>A Fun (IA.SumF 2) [Fun (IA.ProdF 2) [IA.const (divisor_value d),qvar e],rvar e],
    IA.const 0 \<le>\<^sub>I\<^sub>A rvar e,
    rvar e <\<^sub>I\<^sub>A IA.const (abs (divisor_value d))]"

fun constraints where
  "constraints (Var _) = []"
| "constraints (Fun (IA4_Base _) es) = concat (map constraints es)"
| "constraints (Fun IA4_Div [a,d]) = constraints a @ constraints d @ qr_constraints (Fun IA4_Div [a,d]) a d"
| "constraints (Fun IA4_Mod [a,d]) = constraints a @ constraints d @ qr_constraints (Fun IA4_Div [a,d]) a d"
| "constraints _ = []"

lemma qr_constraints_type:
  "IA4.has_type a IA.IntT \<Longrightarrow> f \<in> set (qr_constraints e a d) \<Longrightarrow> IA.formula f"
  by (auto simp: qr_constraints_def IA.is_bool_def less_Suc_eq intro: lower_exp_type)

lemma qr_constraints_satisfied:
  assumes ass: "IA4.assignment alpha" and a: "IA4.has_type a IA.IntT"
    and d: "IA4.has_type d IA.IntT" and closed: "vars_term d = {}"
    and nz: "divisor_value d \<noteq> 0"
  shows "IA.satisfies (lifted_valuation alpha) (Conjunction (qr_constraints (Fun f [a,d]) a d))"
proof -
  from IA4.eval_types[OF ass a] obtain n where av: "IA4.eval a alpha = IA.Int n" by auto
  from IA4.eval_types[OF ass d] obtain k where dv: "IA4.eval d alpha = IA.Int k" by auto
  from constant_eval[OF closed, of "\<lambda>_.IA.Int 0" alpha] dv
  have k: "divisor_value d = k" by (simp add: divisor_value_def)
  from euclid_quot_rem[OF nz[unfolded k], of n] lower_exp_eval[OF a, of alpha]
  show ?thesis by (simp add: qr_constraints_def av dv k IA.is_bool_def algebra_simps)
qed

lemma ia4_child_type:
  "IA4.has_type (Fun g es) ty \<Longrightarrow> e \<in> set es \<Longrightarrow> \<exists>ety. IA4.has_type e ety"
  by (auto simp: set_conv_nth; blast)

lemma constraints_type:
  "IA4.has_type e ty \<Longrightarrow> f \<in> set (constraints e) \<Longrightarrow> IA.formula f"
proof (induct e arbitrary: ty f)
  case (Var x) then show ?case by simp
next
  case (Fun g es)
  show ?case
  proof (cases g)
    case (IA4_Base h)
    with Fun.prems obtain e where mem: "e \<in> set es" and f: "f \<in> set (constraints e)" by auto
    from ia4_child_type[OF Fun.prems(1) mem] obtain ety where typed: "IA4.has_type e ety" by blast
    show ?thesis by (rule Fun.hyps[OF mem typed f])
  next
    case IA4_Div
    with Fun show ?thesis by (cases es rule: list_3_cases, auto simp: less_Suc_eq intro: qr_constraints_type; blast)
  next
    case IA4_Mod
    with Fun show ?thesis by (cases es rule: list_3_cases, auto simp: less_Suc_eq intro: qr_constraints_type; blast)
  qed
qed

lemma constraints_satisfied:
  assumes "IA4.assignment alpha" "IA4.has_type e ty" "supported_exp e"
  shows "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints e))"
  using assms(2-3)
proof (induct e arbitrary: ty)
  case (Var x) then show ?case by simp
next
  case (Fun f es)
  show ?case
  proof (cases f)
    case (IA4_Base g)
    have each: "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints e))" if mem: "e \<in> set es" for e
    proof -
      from ia4_child_type[OF Fun.prems(1) mem] obtain ety where typed: "IA4.has_type e ety" by blast
      from Fun.prems(2) IA4_Base mem have supported: "supported_exp e" by (simp add: list_all_iff)
      show ?thesis by (rule Fun.hyps[OF mem typed supported])
    qed
    with IA4_Base show ?thesis by auto
  next
    case IA4_Div
    with Fun.prems(1) obtain a d where es: "es = [a,d]" by (cases es rule: list_3_cases, auto)
    have a: "IA4.has_type a IA.IntT" and d: "IA4.has_type d IA.IntT"
      using Fun.prems(1) by (simp_all add: IA4_Div es All_less_Suc)
    have sa: "supported_exp a" and sd: "supported_exp d" and closed: "vars_term d = {}" and nz: "divisor_value d \<noteq> 0"
      using Fun.prems(2) by (simp_all add: IA4_Div es)
    have ca: "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints a))"
      by (rule Fun.hyps[OF _ a sa], simp add: es)
    have cd: "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints d))"
      by (rule Fun.hyps[OF _ d sd], simp add: es)
    from ca cd qr_constraints_satisfied[OF assms(1) a d closed nz, of IA4_Div]
    show ?thesis by (auto simp: IA4_Div es)
  next
    case IA4_Mod
    with Fun.prems(1) obtain a d where es: "es = [a,d]" by (cases es rule: list_3_cases, auto)
    have a: "IA4.has_type a IA.IntT" and d: "IA4.has_type d IA.IntT"
      using Fun.prems(1) by (simp_all add: IA4_Mod es All_less_Suc)
    have sa: "supported_exp a" and sd: "supported_exp d" and closed: "vars_term d = {}" and nz: "divisor_value d \<noteq> 0"
      using Fun.prems(2) by (simp_all add: IA4_Mod es)
    have ca: "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints a))"
      by (rule Fun.hyps[OF _ a sa], simp add: es)
    have cd: "IA.satisfies (lifted_valuation alpha) (Conjunction (constraints d))"
      by (rule Fun.hyps[OF _ d sd], simp add: es)
    from ca cd qr_constraints_satisfied[OF assms(1) a d closed nz, of IA4_Div]
    show ?thesis by (auto simp: IA4_Mod es)
  qed
qed
end
