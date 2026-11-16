theory LP_Prolog_Numeric_Return_Guards
 imports LP_Prolog_Stable_Source LP_Prolog_Source_Return_Builtins
begin

fun lpp_success_comparison_code :: "lpp_integer_comparison \<Rightarrow> nat" where
 "lpp_success_comparison_code LPPIntLess = 0"
| "lpp_success_comparison_code LPPIntLessEqual = 1"
| "lpp_success_comparison_code LPPIntEqual = 2"
| "lpp_success_comparison_code LPPIntNotEqual = 3"

lemma lpp_success_comparison_code_exact[simp]:
 "lpp_success_numeric_relation (lpp_success_comparison_code c) n m = lpp_integer_compare c n m"
 by (cases c) (simp_all add: eval_nat_numeral)

definition lpp_numeric_return_guards :: "string \<Rightarrow> nat \<Rightarrow> string lpp_success_guard list option" where
 "lpp_numeric_return_guards f n = (case lpp_source_comparison f of
    None \<Rightarrow> None
  | Some (c,reversed) \<Rightarrow> if n=2 then Some [LPPSNumeric (lpp_success_comparison_code c)
      (Var (if reversed then ''xx'' else ''x''))
      (Var (if reversed then ''x'' else ''xx''))] else None)"

lemma lpp_success_numeric_guard:
 assumes success: "lpp_stable_compare_outcome operation c (lp_ieval a eta) (lp_ieval b eta) (LPPBuiltinSuccess sigma)"
 shows "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta
   (LPPSNumeric (lpp_success_comparison_code c) a b)"
proof -
 obtain u v n d m e where left: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) u"
   and right: "lpp_stable_scalar_evaluation operation (lp_ieval b eta) v"
   and fractions: "lpp_scalar_fraction u n d" "lpp_scalar_fraction v m e"
   and truth: "lpp_integer_compare c (n*e) (m*d)"
   using success by (auto simp: lpp_stable_compare_outcome_def lpp_stable_compare_values_def split: if_splits)
 have ground: "lp_seg_ground (lp_ieval a eta)" "lp_seg_ground (lp_ieval b eta)"
   using lpp_stable_scalar_evaluation_ground[OF left] lpp_stable_scalar_evaluation_ground[OF right] by auto
 have ordered: "lpp_integer_compare c i j"
   if il: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value i)"
     and ir: "lpp_stable_scalar_evaluation operation (lp_ieval b eta) (lpp_integer_value j)" for i j
 proof -
   have returned_values: "u=lpp_integer_value i" "v=lpp_integer_value j"
     using lpp_stable_scalar_evaluation_unique[OF left il] lpp_stable_scalar_evaluation_unique[OF right ir] by auto
   have scalar: "lpp_scalar_fraction (lpp_integer_value i) i 1" "lpp_scalar_fraction (lpp_integer_value j) j 1"
     by (simp_all add: lpp_scalar_fraction_def lpp_integer_value_def)
   have nums: "(n,d)=(i,1)" "(m,e)=(j,1)"
     using lpp_scalar_fraction_unique[OF fractions(1)] lpp_scalar_fraction_unique[OF fractions(2)] scalar returned_values by auto
   show ?thesis using truth nums by simp
 qed
 show ?thesis using ground left right ordered by auto
qed

lemma lpp_success_numeric_guard_integer_relation:
 assumes guard: "lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta (LPPSNumeric c a b)"
   and left: "lpp_stable_scalar_evaluation operation (lp_ieval a eta) (lpp_integer_value n)"
   and right: "lpp_stable_scalar_evaluation operation (lp_ieval b eta) (lpp_integer_value m)"
 shows "lpp_success_numeric_relation c n m"
 using guard lpp_stable_scalar_evaluation_unique[OF _ left]
   lpp_stable_scalar_evaluation_unique[OF _ right] by auto

lemma lpp_numeric_return_guards_sound:
 assumes source: "lpp_stable_source_builtin operation f ts (LPPBuiltinSuccess sigma)"
   and selected: "lpp_numeric_return_guards f (length ts)=Some guards"
 shows "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation)
   (\<lambda>v. map (\<lambda>t. lp_isubst t sigma) ts!(length v-1))) guards"
proof -
 obtain c reversed where comparison: "lpp_source_comparison f=Some (c,reversed)"
   and arity: "length ts=2"
   and guards: "guards=[LPPSNumeric (lpp_success_comparison_code c)
      (Var (if reversed then ''xx'' else ''x'')) (Var (if reversed then ''x'' else ''xx''))]"
   using selected by (auto simp: lpp_numeric_return_guards_def split: option.splits prod.splits if_splits)
 have ordinary: "f\<noteq>''2:is''" using comparison by auto
 have success: "lpp_stable_compare_outcome operation c
     (if reversed then ts!1 else ts!0) (if reversed then ts!0 else ts!1) (LPPBuiltinSuccess sigma)"
   using source comparison ordinary by (auto simp: lpp_stable_source_builtin_def)
 have identity: "sigma=LPIVar"
   using success by (auto simp: lpp_stable_compare_outcome_def split: if_splits)
 show ?thesis using lpp_success_numeric_guard[of operation c
     "Var (if reversed then ''xx'' else ''x'')"
     "\<lambda>v. ts!(length v-1)" "Var (if reversed then ''x'' else ''xx'')" sigma]
   success arity identity by (cases reversed) (simp_all add: guards)
qed

definition lpp_numeric_model_check :: "string lpp_success_clause list \<Rightarrow> string \<Rightarrow> bool" where
 "lpp_numeric_model_check P f = (lpp_numeric_return_guards f 2\<noteq>None \<and>
   list_all (\<lambda>(h,bs,gs). fst h=f \<longrightarrow>
     snd h=lpp_return_builtin_args 2 \<and> bs=[] \<and>
     Some gs=lpp_numeric_return_guards f 2) P)"

lemma lpp_numeric_model_success:
 assumes checked: "lpp_numeric_model_check P f"
   and success: "lpp_guarded_success P E (f,ts)"
 shows "length ts=2 \<and> list_all (lpp_success_guard_holds E (\<lambda>v. ts!(length v-1)))
   (the (lpp_numeric_return_guards f 2))"
 using success
proof cases
 case (clause h bs gs eta)
 have canonical: "snd h=lpp_return_builtin_args 2" "bs=[]"
   "Some gs=lpp_numeric_return_guards f 2" "fst h=f"
   using checked clause by (auto simp: lpp_numeric_model_check_def list_all_iff lpp_success_atom_eval_def)
 have arguments: "ts=[eta ''x'',eta ''xx'']"
   using clause canonical by (simp add: lpp_success_atom_eval_def lpp_return_builtin_args_def eval_nat_numeral)
 obtain c reversed where shape: "gs=[LPPSNumeric (lpp_success_comparison_code c)
   (Var (if reversed then ''xx'' else ''x'')) (Var (if reversed then ''x'' else ''xx''))]"
   using canonical(3) by (auto simp: lpp_numeric_return_guards_def split: option.splits prod.splits if_splits)
 have lookup: "the (lpp_numeric_return_guards f 2)=gs" using canonical(3) by (metis option.sel)
 show ?thesis using clause canonical arguments by (cases reversed) (simp_all add: lookup shape)
qed

ML \<open>
val checked = [@{thm lpp_success_numeric_guard}, @{thm lpp_numeric_return_guards_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted successful numeric guard dependency" else ();
\<close>
end
