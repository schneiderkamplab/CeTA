theory LP_Prolog_Numeric_Return_Calls
 imports LP_Prolog_Numeric_Return_Guards LP_Prolog_Guarded_Receipt LP_Prolog_Evaluated_Integer_Expressions
begin

definition lpp_numeric_call_guards where
 "lpp_numeric_call_guards P b = (if lpp_numeric_model_check P (fst b) \<and> length (snd b)=2
   then map (\<lambda>g. lpp_success_guard_subst g (\<lambda>x. snd b!(length x-1)))
     (the (lpp_numeric_return_guards (fst b) 2)) else [])"

lemma lpp_numeric_call_guards_sound:
 assumes success: "lpp_guarded_success P E (lpp_success_atom_eval b eta)"
 shows "list_all (lpp_success_guard_holds E eta) (lpp_numeric_call_guards P b)"
proof (cases "lpp_numeric_model_check P (fst b) \<and> length (snd b)=2")
 case False then show ?thesis by (auto simp: lpp_numeric_call_guards_def)
next
 case True
 have actual: "lpp_guarded_success P E (fst b,map (\<lambda>t. lp_ieval t eta) (snd b))"
   using success by (simp add: lpp_success_atom_eval_def)
 have guards: "list_all (lpp_success_guard_holds E (\<lambda>x. map (\<lambda>t. lp_ieval t eta) (snd b)!(length x-1)))
     (the (lpp_numeric_return_guards (fst b) 2))"
   using lpp_numeric_model_success[OF True[THEN conjunct1] actual] by simp
 obtain c reversed where shape: "the (lpp_numeric_return_guards (fst b) 2)=
   [LPPSNumeric (lpp_success_comparison_code c) (Var (if reversed then ''xx'' else ''x''))
     (Var (if reversed then ''x'' else ''xx''))]"
   using True by (auto simp: lpp_numeric_model_check_def lpp_numeric_return_guards_def split: option.splits prod.splits if_splits)
 show ?thesis using True guards by (cases reversed) (simp_all add: lpp_numeric_call_guards_def shape)
qed

fun lpp_success_evaluated_integers where
 "lpp_success_evaluated_integers (LPPSInteger t) = [t]"
| "lpp_success_evaluated_integers (LPPSEvaluates e r) = lpp_evaluated_integer_operands e"
| "lpp_success_evaluated_integers (LPPSNumeric c a b) = lpp_evaluated_integer_operands a @ lpp_evaluated_integer_operands b"
| "lpp_success_evaluated_integers g = []"

lemma lpp_success_evaluated_integers_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and guard: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta g"
   and member: "t\<in>set (lpp_success_evaluated_integers g)"
 shows "\<exists>n. lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
 using guard member
 by (cases g; auto simp: lpp_is_integer_def intro: lpp_evaluated_integer_operands_sound[OF compatible]; metis lpp_stable_integer_literal)

definition lpp_numeric_enriched_guards where
 "lpp_numeric_enriched_guards P bs gs = gs @ concat (map (lpp_numeric_call_guards P) bs)"

lemma lpp_numeric_enriched_guards_sound:
 assumes guards: "list_all (lpp_success_guard_holds E eta) gs"
   and helpers: "list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b eta) bs)"
 shows "list_all (lpp_success_guard_holds E eta) (lpp_numeric_enriched_guards P bs gs)"
proof -
 have each: "list_all (lpp_success_guard_holds E eta) (lpp_numeric_call_guards P b)"
   if member: "b\<in>set bs" for b
 proof -
   have actual: "lpp_guarded_success P E (lpp_success_atom_eval b eta)"
     using helpers member by (simp add: list_all_iff)
   show ?thesis by (rule lpp_numeric_call_guards_sound[OF actual])
 qed
 show ?thesis using guards each by (auto simp: lpp_numeric_enriched_guards_def list_all_iff)
qed

lemma lpp_success_invariant_with_calls:
 assumes success: "lpp_guarded_success P E a"
   and clauses: "\<And>h bs gs eta. (h,bs,gs)\<in>set P \<Longrightarrow>
     list_all (lpp_success_guard_holds E eta) gs \<Longrightarrow>
     list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b eta) bs) \<Longrightarrow>
     list_all (\<lambda>b. return_property (lpp_success_atom_eval b eta)) bs \<Longrightarrow>
     return_property (lpp_success_atom_eval h eta)"
 shows "return_property a"
 using success by (induction rule: lpp_guarded_success.induct)
   (auto intro: clauses simp: list_all_iff)

end
