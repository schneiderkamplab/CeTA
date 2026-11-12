theory LP_Prolog_Binary64_NO
 imports LP_Prolog_Binary64_Actions LP_Prolog_NO_Probe_Check LP_Prolog_NO_List
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
proof (induct fuel P action s t rule: lpp_machine_no_step_action.induct)
 case (1 fuel P action s t)
 have included: "lpp_builtin_source P lpp_ground_integer_no_builtin \<subseteq>
   lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_builtin_source_mono)
     (rule lpp_ground_integer_no_stable[OF lpp_binary64_profile_integer_compatible])
 show ?case using 1 included lpp_ground_integer_no_step_sound by auto
next
 case (2 fuel P e s t)

 obtain entry es where st: "s=entry#es"
   using 2 by (cases s) auto
 obtain goals where en: "entry=LPCGoals goals"
   using 2 unfolding st by (cases entry) auto
 obtain goal gs where gl: "goals=goal#gs"
   using 2 unfolding st en by (cases goals) auto
 obtain atom where at: "goal=LPCAtom atom"
   using 2 unfolding st en gl by (cases goal) auto
 obtain symbol args where tm: "atom=Fun symbol args"
   using 2 unfolding st en gl at by (cases atom) auto
 obtain f where sy: "symbol=LPCUser f"
   using 2 unfolding st en gl at tm by (cases symbol) auto
 obtain a tail where ar: "args=a#tail"
   using 2 unfolding st en gl at tm sy by (cases args) auto
 obtain b tail2 where ar2: "tail=b#tail2"
   using 2 unfolding st en gl at tm sy ar by (cases tail) auto
 have ar3: "tail2=[]"
   using 2 unfolding st en gl at tm sy ar ar2 by (cases tail2) auto
 have shape: "s=LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es" by (simp add: st en gl at tm sy ar ar2 ar3)
 have step: "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPMIs e) t"
   using 2 shape by simp
 from step
 obtain v where f: "f=''2:is''" and b: "b=lpp_machine_expression_term e"
   and evaluated: "lpp_machine_evaluate e=Some v"
   and t: "t=(case lpp_machine_unifier a v of None \<Rightarrow> es
       | Some mu \<Rightarrow> LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs)#es)"
   by (auto split: option.splits)
 show ?case using lpp_machine_is_step[OF evaluated, of a gs es P fallback] by (simp add: shape f b t)
next
 case (3 fuel P left right held s t)

 obtain entry es where st: "s=entry#es"
   using 3 by (cases s) auto
 obtain goals where en: "entry=LPCGoals goals"
   using 3 unfolding st by (cases entry) auto
 obtain goal gs where gl: "goals=goal#gs"
   using 3 unfolding st en by (cases goals) auto
 obtain atom where at: "goal=LPCAtom atom"
   using 3 unfolding st en gl by (cases goal) auto
 obtain symbol args where tm: "atom=Fun symbol args"
   using 3 unfolding st en gl at by (cases atom) auto
 obtain f where sy: "symbol=LPCUser f"
   using 3 unfolding st en gl at tm by (cases symbol) auto
 obtain a tail where ar: "args=a#tail"
   using 3 unfolding st en gl at tm sy by (cases args) auto
 obtain b tail2 where ar2: "tail=b#tail2"
   using 3 unfolding st en gl at tm sy ar by (cases tail) auto
 have ar3: "tail2=[]"
   using 3 unfolding st en gl at tm sy ar ar2 by (cases tail2) auto
 have shape: "s=LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es" by (simp add: st en gl at tm sy ar ar2 ar3)
 have step: "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPMCompare left right held) t"
   using 3 shape by simp
 from step
 obtain comparison reversed x y where name: "lpp_source_comparison f=Some (comparison,reversed)"
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
 show ?case unfolding shape t
   by (rule lpp_checked_boolean_step) (use lpp_comparison_selected[OF descriptor] outcome in \<open>simp_all add: numeral_2_eq_2\<close>)
next
 case (4 fuel P v s t)

 obtain entry es where st: "s=entry#es"
   using 4 by (cases s) auto
 obtain goals where en: "entry=LPCGoals goals"
   using 4 unfolding st by (cases entry) auto
 obtain goal gs where gl: "goals=goal#gs"
   using 4 unfolding st en by (cases goals) auto
 obtain atom where at: "goal=LPCAtom atom"
   using 4 unfolding st en gl by (cases goal) auto
 obtain symbol args where tm: "atom=Fun symbol args"
   using 4 unfolding st en gl at by (cases atom) auto
 obtain f where sy: "symbol=LPCUser f"
   using 4 unfolding st en gl at tm by (cases symbol) auto
 obtain a tail where ar: "args=a#tail"
   using 4 unfolding st en gl at tm sy by (cases args) auto
 have ar2: "tail=[]"
   using 4 unfolding st en gl at tm sy ar by (cases tail) auto
 have shape: "s=LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs)#es" by (simp add: st en gl at tm sy ar ar2)
 have step: "lpp_machine_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs)#es) (LPPMInteger v) t"
   using 4 shape by simp
 from step
 have f: "f=''1:integer''" and a: "a=lpp_machine_term v" and valid: "lpp_machine_valid v"
   and t: "t=(if lpp_machine_is_integer v then LPCGoals gs#es else es)" by auto
 show ?case unfolding shape f a t
   by (rule lpp_checked_boolean_step)
     (use lpp_machine_integer_test[OF valid] in \<open>simp_all add: lpp_builtin_signature_def lpp_machine_term_eval\<close>)
qed (simp_all add: lpp_no_plain_probe_sound lpp_no_plain_list_sound)

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
