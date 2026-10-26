theory IA4_Definability
  imports IA4_Checker
begin

fun ia4_defining_equation where
  "ia4_defining_equation x ty (Atom (Fun (IA4_Base IA.EqF) [Var (y,t),e])) =
    (x=y \<and> ty=t \<and> ty=IA.IntT \<and> IA4.has_type e IA.IntT \<and> (x,ty) \<notin> vars_term e)"
| "ia4_defining_equation _ _ _ = False"


lemma ia4_defining_equation:
  fixes f :: "'v ia4_exp formula" and alpha :: "'v \<times> IA.ty \<Rightarrow> IA.val"
  assumes "ia4_defining_equation x ty f" "IA4.assignment alpha"
  shows "\<exists>a\<in>IA.Values_of_type ty. IA4.satisfies (alpha((x,ty):=a)) f"
  using assms(1)
proof (cases "(x,ty,f)" rule: ia4_defining_equation.cases)
  case (1 xx tt y t e)
  from 1 assms(1) have typed: "IA4.has_type e IA.IntT" and fresh: "(x,ty) \<notin> vars_term e" and ids: "x=y" "ty=t" "ty=IA.IntT" by auto
  from IA4.eval_types[OF assms(2) typed] obtain n where v: "IA4.eval e alpha = IA.Int n" by auto
  show ?thesis
    by (rule bexI[of _ "IA.Int n"], insert 1 ids fresh v, auto)
qed (insert assms(1), auto)

fun ia4_definable where
  "ia4_definable x ty (Conjunction []) = True"
| "ia4_definable x ty (Conjunction [f]) = ia4_defining_equation x ty f"
| "ia4_definable x ty f = ia4_defining_equation x ty f"

definition ia4_def_checker where
  "ia4_def_checker x ty f = check (ia4_definable x ty f)
    (showsl_lit (STR ''fresh variable definition requires an independent typed equation''))"

lemma ia4_def_checker_sound:
  fixes f :: "'v ia4_exp formula" and alpha :: "'v \<times> IA.ty \<Rightarrow> IA.val"
  assumes "isOK (ia4_def_checker x ty f)" "IA4.assignment alpha"
  shows "\<exists>a\<in>IA.Values_of_type ty. IA4.satisfies (alpha((x,ty):=a)) f"
proof -
  have one: "ia4_defining_equation x ty g \<Longrightarrow> \<exists>a\<in>IA.Values_of_type ty. IA4.satisfies (alpha((x,ty):=a)) g" for g
    by (rule ia4_defining_equation[OF _ assms(2)])
  show ?thesis
    using assms(1)[unfolded ia4_def_checker_def] IA4.assignmentD[OF assms(2), of "(x,ty)"]
    by (cases "(x,ty,f)" rule: ia4_definable.cases; auto dest!: one)
qed

end
