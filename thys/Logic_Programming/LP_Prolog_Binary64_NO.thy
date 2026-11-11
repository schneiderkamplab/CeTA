theory LP_Prolog_Binary64_NO
 imports LP_Prolog_Binary64_Actions
begin

lemma lpp_machine_comparison_value:
 assumes left: "lpp_machine_evaluate a=Some x" and right: "lpp_machine_evaluate b=Some y"
 shows "lpp_stable_compare_values (lpp_binary64_profile_operation fallback) comparison
   (lp_ieval (lpp_machine_expression_term a) eta) (lp_ieval (lpp_machine_expression_term b) eta)
   (lpp_integer_compare comparison (fst (lpp_machine_fraction x) * snd (lpp_machine_fraction y))
     (fst (lpp_machine_fraction y) * snd (lpp_machine_fraction x)))"
 by (rule lpp_stable_compare_values_exact[OF lpp_machine_evaluation_sound[OF left]
   lpp_machine_evaluation_sound[OF right]
   lpp_machine_scalar_fraction[OF lpp_machine_evaluate_valid[OF left]]
   lpp_machine_scalar_fraction[OF lpp_machine_evaluate_valid[OF right]], THEN iffD2]) simp

lemma lpp_machine_no_step_sound:
 "lpp_machine_no_step fuel P s action t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof (induct fuel P s action t rule: lpp_machine_no_step.induct)
 case (1 fuel P s action t)
 have included: "lpp_builtin_source P lpp_ground_integer_no_builtin \<subseteq>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_builtin_source_mono)
     (rule lpp_ground_integer_no_stable[OF lpp_binary64_profile_integer_compatible])
 show ?case using 1 included lpp_ground_integer_no_step_sound by auto
next
 case (2 fuel P f a b gs es e t)
 then obtain v where f: "f=''2:is''" and b: "b=lpp_machine_expression_term e"
   and evaluated: "lpp_machine_evaluate e=Some v"
   and t: "t=(case lpp_machine_unifier a v of None \<Rightarrow> es
       | Some mu \<Rightarrow> LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs)#es)"
   by (auto split: option.splits)
 show ?case using lpp_machine_is_step[OF evaluated, of a gs es P fallback] by (simp add: f b t)
next
 case (4 fuel P f a b gs es left right held t)
 then obtain comparison reversed x y where name: "lpp_source_comparison f=Some (comparison,reversed)"
   and left: "lpp_machine_evaluate left=Some x" and right: "lpp_machine_evaluate right=Some y"
   and a: "a=lpp_machine_expression_term left" and b: "b=lpp_machine_expression_term right"
   and held: "held=lpp_integer_compare comparison
     (fst (lpp_machine_fraction (if reversed then y else x)) * snd (lpp_machine_fraction (if reversed then x else y)))
     (fst (lpp_machine_fraction (if reversed then x else y)) * snd (lpp_machine_fraction (if reversed then y else x)))"
   and t: "t=(if held then LPCGoals gs#es else es)"
   by (auto simp: Let_def split: option.splits prod.splits)
 have descriptor: "lpp_comparison_descriptor f comparison reversed"
   using name lpp_source_comparison_descriptor by blast
 have compared: "lpp_stable_compare_values (lpp_binary64_profile_operation fallback) comparison
   (if reversed then lp_ieval b LPIVar else lp_ieval a LPIVar)
   (if reversed then lp_ieval a LPIVar else lp_ieval b LPIVar) held"
   using lpp_machine_comparison_value[OF left right, where eta=LPIVar and comparison=comparison and fallback=fallback]
     lpp_machine_comparison_value[OF right left, where eta=LPIVar and comparison=comparison and fallback=fallback]
   by (cases reversed) (simp_all add: a b held)
 have outcome: "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback) f
   [lp_ieval a LPIVar,lp_ieval b LPIVar] (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
   by (rule lpp_stable_source_comparison_evaluated[OF lpp_binary64_profile_integer_compatible descriptor compared])
 show ?case unfolding t
   by (rule lpp_checked_boolean_step) (use lpp_comparison_selected[OF descriptor] outcome in \<open>simp_all add: numeral_2_eq_2\<close>)
next
 case (6 fuel P f a gs es v t)
 then have f: "f=''1:integer''" and a: "a=lpp_machine_term v" and valid: "lpp_machine_valid v"
   and t: "t=(if lpp_machine_is_integer v then LPCGoals gs#es else es)" by auto
 show ?case unfolding f a t
   by (rule lpp_checked_boolean_step)
     (use lpp_machine_integer_test[OF valid] in \<open>simp_all add: lpp_builtin_signature_def lpp_machine_term_eval\<close>)
qed simp_all

definition lpp_machine_no_check_source where
 "lpp_machine_no_check_source fuel P q modes argv a before after initial_steps steps =
   lpp_builtin_trace_checker.check_source P (lpp_machine_no_step fuel P) q modes argv a before after initial_steps steps"

theorem lpp_machine_no_check_source_sound:
 assumes "lpp_machine_no_check_source fuel P q modes argv a before after initial_steps steps"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 interpret trace: lpp_builtin_trace_checker P
   "lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)" "lpp_machine_no_step fuel P"
   by unfold_locales (rule lpp_machine_no_step_sound)
 show ?thesis using assms trace.check_source_sound by (simp add: lpp_machine_no_check_source_def)
qed

ML \<open>
val checked = [@{thm lpp_machine_no_check_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted binary64 source-loop dependency" else ();
\<close>
end
