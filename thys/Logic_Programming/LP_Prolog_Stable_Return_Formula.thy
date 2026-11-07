theory LP_Prolog_Stable_Return_Formula
 imports LP_Prolog_Stable_Return_Constraints LP_Prolog_Stable_Constrained_Valuation
begin

abbreviation lpp_return_le where
  "lpp_return_le a b \<equiv> lpp_numeric_condition_formula (LPPIntLessEqual,a,b)"
abbreviation lpp_return_lt where
  "lpp_return_lt a b \<equiv> lpp_numeric_condition_formula (LPPIntLess,a,b)"

fun lpp_return_formula where
  "lpp_return_formula rename ps (LPPReturnNonnegative t) =
    lpp_return_le (LPPEConstant 0) (LPPEVariable (rename t))"
| "lpp_return_formula rename ps (LPPReturnConstant n) =
    lpp_numeric_condition_formula (LPPIntEqual,LPPEVariable (rename (lpp_integer_term n)),LPPEConstant (abs n*lpp_scalar_scale))"
| "lpp_return_formula rename ps (LPPReturnQuotient a b) =
    lpp_return_le (LPPEVariable (rename (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]))) (LPPEVariable (rename a))"
| "lpp_return_formula rename ps (LPPReturnStrictQuotient a b) =
    Disjunction [lpp_return_le (LPPEVariable (rename b)) (LPPEConstant lpp_scalar_scale),
      lpp_return_le (LPPEVariable (rename a)) (LPPEConstant 0),
      lpp_return_lt (LPPEVariable (rename (Fun (LPCUser ''2:prolog_data_2f2f'') [a,b]))) (LPPEVariable (rename a))]"
| "lpp_return_formula rename ps (LPPReturnHelper i j) =
    Disjunction (lpp_return_le (LPPEVariable (rename (snd (ps!i)!j))) (LPPEConstant 0) #
      map (\<lambda>t. lpp_return_le (LPPEVariable (rename (snd (ps!i)!j))) (LPPEVariable (rename t)))
        (lpp_magnitude_inputs j (snd (ps!i))))"

fun lpp_return_terms where
  "lpp_return_terms ps (LPPReturnNonnegative t) = [t]"
| "lpp_return_terms ps (LPPReturnConstant n) = [lpp_integer_term n]"
| "lpp_return_terms ps (LPPReturnQuotient a b) = [Fun (LPCUser ''2:prolog_data_2f2f'') [a,b],a]"
| "lpp_return_terms ps (LPPReturnStrictQuotient a b) = [Fun (LPCUser ''2:prolog_data_2f2f'') [a,b],a,b]"
| "lpp_return_terms ps (LPPReturnHelper i j) = snd (ps!i)!j # lpp_magnitude_inputs j (snd (ps!i))"

lemma lpp_magnitude_max_disjunction:
  "r\<le>lpp_magnitude_max operation ts \<longleftrightarrow>
    r\<le>0 \<or> (\<exists>t\<in>set ts. r\<le>abs (lpp_stable_scaled_bound operation t))"
  by (induction ts) auto

lemma lpp_return_formula_typed:
  "IA4.formula (lpp_return_formula rename ps constraint)"
  by (cases constraint) (auto simp: lpp_comparison_its_type lpp_expression_its_type less_Suc_eq list_all_iff)

lemma lpp_return_formula_value:
  assumes assigned: "\<And>t. t\<in>set (lpp_return_terms ps constraint) \<Longrightarrow>
    rho (rename t)=abs (lpp_stable_scaled_bound operation (lp_ieval t eta))"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_return_formula rename ps constraint) =
    lpp_return_constraint_holds operation eta ps constraint"
  using assigned
  by (cases constraint) (auto simp: lpp_comparison_typed_assignment lpp_magnitude_max_disjunction list_ex_iff)

theorem lpp_checked_return_formula:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_magnitude_program summaries P receipts"
    and checked: "lpp_check_return_constraint summaries ps constraint"
    and success: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>a. lpp_success_atom_eval a eta) ps)"
    and assigned: "\<And>t. t\<in>set (lpp_return_terms ps constraint) \<Longrightarrow>
      rho (rename t)=abs (lpp_stable_scaled_bound operation (lp_ieval t eta))"
  shows "IA4.satisfies (lpp_integer_assignment rho) (lpp_return_formula rename ps constraint)"
  using lpp_check_return_constraint_sound[OF compatible program checked success]
    lpp_return_formula_value[where ps=ps and constraint=constraint and rho=rho and rename=rename and operation=operation and eta=eta, OF assigned] by blast

ML \<open>
val checked = [@{thm lpp_checked_return_formula}, @{thm lpp_return_formula_typed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted return formula dependency" else ();
\<close>
end
