theory LP_Prolog_Integer_Recurrence_Relation
  imports LP_Prolog_Integer_Recurrence_Iteration LP_Prolog_Numeric_Path
begin

text \<open>Symbolic execution binds the integer child to the ordered source
recipe. Assignment expressions are substituted at their source position;
guards retain their original operands and orientation. The equivalence below
is required in both directions, unlike a termination overapproximation.\<close>

fun lpp_recurrence_substitute where
  "lpp_recurrence_substitute env (LPPEConstant n) = LPPEConstant n"
| "lpp_recurrence_substitute env (LPPEVariable x) = env x"
| "lpp_recurrence_substitute env (LPPEPositive a) = LPPEPositive (lpp_recurrence_substitute env a)"
| "lpp_recurrence_substitute env (LPPENegate a) = LPPENegate (lpp_recurrence_substitute env a)"
| "lpp_recurrence_substitute env (LPPEAdd a b) = LPPEAdd (lpp_recurrence_substitute env a) (lpp_recurrence_substitute env b)"
| "lpp_recurrence_substitute env (LPPESubtract a b) = LPPESubtract (lpp_recurrence_substitute env a) (lpp_recurrence_substitute env b)"
| "lpp_recurrence_substitute env (LPPEMultiply a b) = LPPEMultiply (lpp_recurrence_substitute env a) (lpp_recurrence_substitute env b)"
| "lpp_recurrence_substitute env (LPPEDivide a d) = LPPEDivide (lpp_recurrence_substitute env a) d"
| "lpp_recurrence_substitute env (LPPEModulo a d) = LPPEModulo (lpp_recurrence_substitute env a) d"

lemma lpp_recurrence_substitute_value:
  "lpp_expression_value (lpp_recurrence_substitute env e) rho =
    lpp_expression_value e (\<lambda>x. lpp_expression_value (env x) rho)"
  by (induct e) simp_all

fun lpp_recurrence_symbolic_values where
  "lpp_recurrence_symbolic_values [] env = env"
| "lpp_recurrence_symbolic_values (LPPRSet x e#ops) env =
    lpp_recurrence_symbolic_values ops (env(x:=lpp_recurrence_substitute env e))"
| "lpp_recurrence_symbolic_values (LPPRGuard f c reversed a b#ops) env =
    lpp_recurrence_symbolic_values ops env"

fun lpp_recurrence_symbolic_guards where
  "lpp_recurrence_symbolic_guards [] env = []"
| "lpp_recurrence_symbolic_guards (LPPRSet x e#ops) env =
    lpp_recurrence_symbolic_guards ops (env(x:=lpp_recurrence_substitute env e))"
| "lpp_recurrence_symbolic_guards (LPPRGuard f c reversed a b#ops) env =
    (c,lpp_recurrence_substitute env (if reversed then b else a),
       lpp_recurrence_substitute env (if reversed then a else b)) #
    lpp_recurrence_symbolic_guards ops env"

lemma lpp_recurrence_symbolic_values_exact:
  "(\<lambda>x. lpp_expression_value (lpp_recurrence_symbolic_values ops env x) rho) =
    lpp_recurrence_values ops (\<lambda>x. lpp_expression_value (env x) rho)"
proof (induct ops arbitrary: env)
  case Nil show ?case by simp
next
  case (Cons op ops)
  have update: "(\<lambda>v. lpp_expression_value ((env(x:=lpp_recurrence_substitute env e)) v) rho) =
    (\<lambda>v. lpp_expression_value (env v) rho)(x:=lpp_expression_value e (\<lambda>v. lpp_expression_value (env v) rho))"
    for x e by (rule ext) (simp add: lpp_recurrence_substitute_value)
  show ?case by (cases op) (simp_all only: lpp_recurrence_symbolic_values.simps lpp_recurrence_values.simps Cons.hyps update)
qed

lemma lpp_recurrence_symbolic_guards_exact:
  "list_all (lpp_numeric_condition_holds rho) (lpp_recurrence_symbolic_guards ops env) =
    lpp_recurrence_guards ops (\<lambda>x. lpp_expression_value (env x) rho)"
proof (induct ops arbitrary: env)
  case Nil show ?case by simp
next
  case (Cons op ops)
  have update: "(\<lambda>v. lpp_expression_value ((env(x:=lpp_recurrence_substitute env e)) v) rho) =
    (\<lambda>v. lpp_expression_value (env v) rho)(x:=lpp_expression_value e (\<lambda>v. lpp_expression_value (env v) rho))"
    for x e by (rule ext) (simp add: lpp_recurrence_substitute_value)
  show ?case by (cases op) (simp_all only: lpp_recurrence_symbolic_guards.simps lpp_recurrence_guards.simps list_all_Cons_iff list_all_Nil_iff lpp_numeric_condition_holds.simps Cons.hyps update lpp_recurrence_substitute_value)
qed

definition lpp_recurrence_guard_formula where
  "lpp_recurrence_guard_formula ops = Conjunction
    (map lpp_numeric_condition_formula (lpp_recurrence_symbolic_guards ops LPPEVariable))"

lemma lpp_recurrence_condition_formula_exact[simp]:
  "IA4.satisfies (lpp_integer_assignment rho) (lpp_numeric_condition_formula condition) =
    lpp_numeric_condition_holds rho condition"
  by (cases condition) (simp add: lpp_comparison_typed_assignment split: prod.splits)

lemma lpp_recurrence_guard_formula_exact:
  "IA4.satisfies (lpp_integer_assignment rho) (lpp_recurrence_guard_formula ops) =
    lpp_recurrence_guards ops rho"
  using lpp_recurrence_symbolic_guards_exact[of rho ops LPPEVariable]
  by (simp add: lpp_recurrence_guard_formula_def list_all_iff lpp_comparison_typed_assignment
    split: prod.splits)

definition lpp_recurrence_relation_formula where
  "lpp_recurrence_relation_formula xs ops outputs = Conjunction
    (map lpp_numeric_condition_formula
      (map (lpp_rename_numeric_condition Pre)
        (lpp_recurrence_symbolic_guards ops LPPEVariable) @
       map (\<lambda>(x,e). (LPPIntEqual, LPPEVariable (Post x),
         map_lpp_integer_expression Pre (lpp_recurrence_substitute
           (lpp_recurrence_symbolic_values ops LPPEVariable) e))) (zip xs outputs)))"

lemma lpp_recurrence_relation_formula_exact:
  assumes lengths: "length xs=length outputs"
  shows "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after middle))
      (lpp_recurrence_relation_formula xs ops outputs) =
    (lpp_recurrence_guards ops before \<and>
      map after xs=map (\<lambda>e. lpp_expression_value e (lpp_recurrence_values ops before)) outputs)"
proof -
  have symbolic: "(\<lambda>x. lpp_expression_value
      (lpp_recurrence_symbolic_values ops LPPEVariable x) before) =
      lpp_recurrence_values ops before"
    using lpp_recurrence_symbolic_values_exact[of ops LPPEVariable before] by simp
  have outputs: "(\<forall>(x,e)\<in>set (zip xs outputs).
      after x=lpp_expression_value e (lpp_recurrence_values ops before)) =
      (map after xs=map (\<lambda>e. lpp_expression_value e (lpp_recurrence_values ops before)) outputs)"
    using lengths by (auto simp: list_eq_iff_zip_eq zip_map1 zip_map2 split: prod.splits)
  have guards: "list_all (lpp_numeric_condition_holds before)
      (lpp_recurrence_symbolic_guards ops LPPEVariable)=lpp_recurrence_guards ops before"
    using lpp_recurrence_symbolic_guards_exact[of before ops LPPEVariable] by simp
  have expanded: "IA4.satisfies (lpp_integer_assignment (lpp_trans_integer before after middle))
      (lpp_recurrence_relation_formula xs ops outputs) =
    (list_all (lpp_numeric_condition_holds before) (lpp_recurrence_symbolic_guards ops LPPEVariable) \<and>
      (\<forall>(x,e)\<in>set (zip xs outputs).
        after x=lpp_expression_value e (lpp_recurrence_values ops before)))"
    by (auto simp: lpp_recurrence_relation_formula_def lpp_comparison_typed_assignment
      lpp_rename_numeric_condition_holds lpp_expression_typed_assignment algebra.eval.simps
      lpp_expression_rename_value lpp_recurrence_substitute_value o_def symbolic
      list_all_iff ball_Un split: prod.splits)
  show ?thesis using expanded by (simp only: guards outputs)
qed

ML \<open>
val checked = [@{thm lpp_recurrence_symbolic_values_exact},
  @{thm lpp_recurrence_guard_formula_exact}, @{thm lpp_recurrence_relation_formula_exact}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted exact recurrence relation dependency" else ();
\<close>
end
