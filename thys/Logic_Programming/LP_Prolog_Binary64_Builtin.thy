theory LP_Prolog_Binary64_Builtin
 imports LP_Prolog_Binary64_Evaluation LP_Prolog_Stable_Builtin_Evidence LP_Prolog_Ground_Integer_NO_Profile
begin

lemma lpp_machine_value_name:
 "\<exists>f. lpp_machine_value v=LPIFun (LPCUser f) []"
 by (cases v) (simp_all add: lpp_integer_value_def lpp_binary64_value_def)

fun lpp_machine_name where
 "lpp_machine_name (LPPMachineInteger n)=lpp_integer_name n"
| "lpp_machine_name (LPPMachineFloat b)=lpp_binary64_name b"
lemma lpp_machine_value_named:
 "lpp_machine_value v=LPIFun (LPCUser (lpp_machine_name v)) []"
 by (cases v) (simp_all add: lpp_integer_value_def lpp_binary64_value_def)

lemma lpp_stable_source_is_evaluated:
 assumes compatible: "lpp_stable_integer_operations operation"
   and evaluated: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
 shows "lpp_stable_source_builtin operation ''2:is'' [a,e]
  (case lpp_scalar_unifier a f of None \<Rightarrow> LPPBuiltinFailure | Some mu \<Rightarrow> LPPBuiltinSuccess mu)"
 using lpp_stable_is_evaluated[OF compatible evaluated]
 by (simp add: lpp_stable_source_builtin_def lpp_finite_source_builtin_def lpp_stable_is_outcome_def)

lemma lpp_stable_source_comparison_evaluated:
 assumes compatible: "lpp_stable_integer_operations operation"
   and name: "lpp_comparison_descriptor f comparison reversed"
   and compared: "lpp_stable_compare_values operation comparison
     (if reversed then b else a) (if reversed then a else b) truth"
 shows "lpp_stable_source_builtin operation f [a,b]
   (if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
proof -
 let ?out="if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure"
 have observation: "lpp_stable_compare_outcome operation comparison
   (if reversed then b else a) (if reversed then a else b) ?out"
   by (rule lpp_stable_comparison_evaluated[OF compatible compared])
 have ground: "lp_seg_ground a" "lp_seg_ground b"
   using compared lpp_stable_scalar_evaluation_ground
   by (cases reversed; auto simp: lpp_stable_compare_values_def)+
 have nc: "lpp_source_comparison f=Some (comparison,reversed)"
   using name lpp_source_comparison_descriptor by blast
 have ni: "f\<noteq>''2:is''" and nt: "f\<noteq>''1:integer''"
   using name by (cases comparison; cases reversed; auto)+
 have domain: "lpp_integer_source_domain f [a,b]"
   using ground by (simp only: lpp_integer_source_domain.simps ni nt if_False nc option.case; simp)
 have finite: "lpp_finite_source_builtin f [a,b] ?out"
   using lpp_stable_compare_refines_finite[OF observation]
   by (simp only: lpp_finite_source_integer_domain[OF domain]
       lpp_integer_source_finite_comparison[OF name])
 show ?thesis using finite observation
   by (simp only: lpp_stable_source_builtin_def ni if_False nc option.case prod.case; auto split: if_splits)
qed

fun lpp_machine_unifier where
 "lpp_machine_unifier (Var x) v=Some (Var(x:=lpp_machine_term v))"
| "lpp_machine_unifier (Fun f ts) v=
    (if Fun f ts=lpp_machine_term v then Some Var else None)"

lemma lpp_machine_unifier_evaluation:
 assumes scalar_value: "lpp_machine_value v=LPIFun (LPCUser f) []"
 shows "map_option (\<lambda>mu x. lp_ieval (mu x) LPIVar) (lpp_machine_unifier a v) =
   lpp_scalar_unifier (lp_ieval a LPIVar) f"
 using scalar_value
 by (cases a; cases v)
   (auto simp: lpp_integer_term_def lpp_integer_value_def lpp_binary64_value_def
     fun_eq_iff split: if_splits)

ML \<open>
val checked = [@{thm lpp_stable_source_is_evaluated},
 @{thm lpp_stable_source_comparison_evaluated}, @{thm lpp_machine_unifier_evaluation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 builtin dependency" else ();
\<close>
end
