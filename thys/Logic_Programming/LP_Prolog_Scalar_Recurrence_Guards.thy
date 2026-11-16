theory LP_Prolog_Scalar_Recurrence_Guards
 imports LP_Prolog_Scalar_Expression_Templates LP_Prolog_Binary64_Builtin
begin

datatype lpp_scalar_guard =
    LPPScalarCompare string lpp_scalar_template lpp_scalar_template
  | LPPScalarIsLiteral lpp_machine_scalar lpp_scalar_template

fun lpp_scalar_guard_symbol where
 "lpp_scalar_guard_symbol (LPPScalarCompare f a b) = f"
| "lpp_scalar_guard_symbol (LPPScalarIsLiteral v e) = ''2:is''"
fun lpp_scalar_guard_terms where
 "lpp_scalar_guard_terms (LPPScalarCompare f a b) =
    [lpp_scalar_template_term a,lpp_scalar_template_term b]"
| "lpp_scalar_guard_terms (LPPScalarIsLiteral v e) =
    [lpp_machine_term v,lpp_scalar_template_term e]"

definition lpp_scalar_guard_goal where
 "lpp_scalar_guard_goal g = LPCAtom (Fun (LPCUser (lpp_scalar_guard_symbol g)) (lpp_scalar_guard_terms g))"

fun lpp_scalar_guard_check where
 "lpp_scalar_guard_check value_table (LPPScalarCompare f a b) =
    (case (lpp_source_comparison f,lpp_scalar_template_evaluate value_table a,
       lpp_scalar_template_evaluate value_table b) of
      (Some (c,reversed),Some x,Some y) \<Rightarrow>
        (let left = lpp_machine_fraction (if reversed then y else x);
             right = lpp_machine_fraction (if reversed then x else y)
         in Some (lpp_integer_compare c (fst left * snd right) (fst right * snd left)))
    | _ \<Rightarrow> None)"
| "lpp_scalar_guard_check value_table (LPPScalarIsLiteral w e) =
    (if lpp_machine_valid w then
      map_option (\<lambda>v. lpp_machine_name w = lpp_machine_name v)
        (lpp_scalar_template_evaluate value_table e)
     else None)"

lemma lpp_scalar_template_comparison:
 assumes left: "lpp_scalar_template_evaluate value_table a=Some x"
   and right: "lpp_scalar_template_evaluate value_table b=Some y"
   and parameters: "\<And>z w. value_table z=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta z) (lpp_machine_value w)"
 shows "lpp_stable_compare_values (lpp_binary64_profile_operation fallback) comparison
   (lp_ieval (lpp_scalar_template_term a) eta) (lp_ieval (lpp_scalar_template_term b) eta)
   (lpp_integer_compare comparison (fst (lpp_machine_fraction x) * snd (lpp_machine_fraction y))
     (fst (lpp_machine_fraction y) * snd (lpp_machine_fraction x)))"
 by (rule lpp_stable_compare_values_exact[OF lpp_scalar_template_sound[OF left parameters]
   lpp_scalar_template_sound[OF right parameters]
   lpp_machine_scalar_fraction[OF lpp_scalar_template_valid[OF left]]
   lpp_machine_scalar_fraction[OF lpp_scalar_template_valid[OF right]], THEN iffD2]) simp_all

lemma lpp_scalar_guard_checked_signature:
 "lpp_scalar_guard_check value_table g=Some held \<Longrightarrow>
   (lpp_scalar_guard_symbol g,length (lpp_scalar_guard_terms g))\<in>lpp_builtin_signature"
 by (cases g) (auto simp: lpp_builtin_signature_def
   split: option.splits prod.splits if_splits dest: lpp_source_comparison_descriptor[THEN iffD1])

lemma lpp_scalar_guard_sound:
 assumes checked: "lpp_scalar_guard_check value_table g=Some held"
   and parameters: "\<And>x w. value_table x=Some w \<Longrightarrow>
     lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback) (eta x) (lpp_machine_value w)"
 shows "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)
   (lpp_scalar_guard_symbol g) (map (\<lambda>t. lp_ieval t eta) (lpp_scalar_guard_terms g))
   (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
proof (cases g)
 case (LPPScalarCompare f a b)
 obtain c reversed x y where name: "lpp_source_comparison f=Some (c,reversed)"
   and left: "lpp_scalar_template_evaluate value_table a=Some x"
   and right: "lpp_scalar_template_evaluate value_table b=Some y"
   and held: "held=lpp_integer_compare c
      (fst (lpp_machine_fraction (if reversed then y else x)) * snd (lpp_machine_fraction (if reversed then x else y)))
      (fst (lpp_machine_fraction (if reversed then x else y)) * snd (lpp_machine_fraction (if reversed then y else x)))"
   using checked by (auto simp: LPPScalarCompare Let_def split: option.splits prod.splits)
 have descriptor: "lpp_comparison_descriptor f c reversed"
   using name by (simp only: lpp_source_comparison_descriptor)
 have compared: "lpp_stable_compare_values (lpp_binary64_profile_operation fallback) c
     (if reversed then lp_ieval (lpp_scalar_template_term b) eta else lp_ieval (lpp_scalar_template_term a) eta)
     (if reversed then lp_ieval (lpp_scalar_template_term a) eta else lp_ieval (lpp_scalar_template_term b) eta) held"
   using lpp_scalar_template_comparison[OF left right parameters, where comparison=c]
     lpp_scalar_template_comparison[OF right left parameters, where comparison=c] held
   by (cases reversed) simp_all
 show ?thesis using lpp_stable_source_comparison_evaluated[OF
   lpp_binary64_profile_integer_compatible descriptor compared]
   by (simp add: LPPScalarCompare)
next
 case (LPPScalarIsLiteral w e)
 obtain v where evaluated: "lpp_scalar_template_evaluate value_table e=Some v"
   and held: "held=(lpp_machine_name w=lpp_machine_name v)"
   using checked by (auto simp: LPPScalarIsLiteral split: option.splits if_splits)
 have eval: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
    (lp_ieval (lpp_scalar_template_term e) eta) (LPIFun (LPCUser (lpp_machine_name v)) [])"
   using lpp_scalar_template_sound[OF evaluated parameters] by (simp only: lpp_machine_value_named)
 show ?thesis using lpp_stable_source_is_evaluated[OF lpp_binary64_profile_integer_compatible eval,
   of "lp_ieval (lpp_machine_term w) eta"]
   by (auto simp: LPPScalarIsLiteral lpp_machine_term_eval lpp_machine_value_named held split: if_splits)
qed

ML \<open>
val checked = [@{thm lpp_scalar_guard_sound}, @{thm lpp_scalar_guard_checked_signature}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence guard dependency" else ();
\<close>
end
