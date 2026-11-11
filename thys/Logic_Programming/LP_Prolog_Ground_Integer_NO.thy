theory LP_Prolog_Ground_Integer_NO
 imports LP_Prolog_Checked_Builtin_Trace LP_Prolog_Integer_Source LP_Prolog_Arithmetic
begin

text \<open>A checked subset of the existing builtin transitions, adding only
integer comparison outcomes. A ground term is not assumed to be an integer;
both expression receipts must check with an empty variable domain.\<close>

definition lpp_ground_integer_no_builtin where
 "lpp_ground_integer_no_builtin f ts outcome =
  (lpp_integer_no_builtin f ts outcome \<or>
   (\<exists>comparison reversed a b. ts=[a,b] \<and>
     lpp_comparison_descriptor f comparison reversed \<and>
     lpp_integer_compare_outcome comparison (if reversed then b else a) (if reversed then a else b) outcome))"

datatype lpp_ground_integer_no_action =
 LPPGIBase lpp_integer_no_action |
 LPPGICompare "string lpp_integer_expression" "string lpp_integer_expression" bool

fun lpp_ground_integer_no_step where
 "lpp_ground_integer_no_step fuel P s (LPPGIBase action) t = lpp_integer_no_step fuel P s action t"
| "lpp_ground_integer_no_step fuel P (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) (LPPGICompare left right held) t =
  (a=lpp_expression_term left \<and> b=lpp_expression_term right \<and>
   lpp_expression_check [] left \<and> lpp_expression_check [] right \<and>
   (case lpp_source_comparison f of None \<Rightarrow> False | Some (comparison,reversed) \<Rightarrow>
    held=lpp_integer_compare comparison
      (lpp_expression_value (if reversed then right else left) (\<lambda>_. 0))
      (lpp_expression_value (if reversed then left else right) (\<lambda>_. 0))) \<and>
   t=(if held then LPCGoals gs#es else es))"
| "lpp_ground_integer_no_step fuel P s (LPPGICompare left right held) t = False"

lemma lpp_ground_integer_comparison_step:
 assumes selected: "(f,2)\<in>lpp_builtin_signature"
   and outcome: "lpp_ground_integer_no_builtin f [lp_ieval a LPIVar,lp_ieval b LPIVar]
     (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 shows "(lp_cut_state_eval (LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs)#es) LPIVar,
   lp_cut_state_eval (if held then LPCGoals gs#es else es) LPIVar)\<in>
   lpp_builtin_source P lpp_ground_integer_no_builtin"
proof (cases held)
 case True
 have out: "lpp_ground_integer_no_builtin f [lp_ieval a LPIVar,lp_ieval b LPIVar] (LPPBuiltinSuccess LPIVar)"
   using outcome True by simp
 show ?thesis using lpp_atomic_source.success[where U=lpp_ground_integer_no_builtin and f=f
   and ts="[lp_ieval a LPIVar,lp_ieval b LPIVar]" and sigma=LPIVar and P=P and B=lpp_builtin_signature
   and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF out] selected
   by (auto simp: True lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def numeral_2_eq_2)
next
 case False
 have out: "lpp_ground_integer_no_builtin f [lp_ieval a LPIVar,lp_ieval b LPIVar] LPPBuiltinFailure"
   using outcome False by simp
 show ?thesis using lpp_atomic_source.failure[where U=lpp_ground_integer_no_builtin and f=f
   and ts="[lp_ieval a LPIVar,lp_ieval b LPIVar]" and P=P and B=lpp_builtin_signature
   and gs="map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
   and es="map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar)) es", OF out] selected
   by (auto simp: False lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def numeral_2_eq_2)
qed

lemma lpp_ground_integer_no_step_sound:
 "lpp_ground_integer_no_step fuel P s action t \<Longrightarrow>
  (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>lpp_builtin_source P lpp_ground_integer_no_builtin"
proof (induct fuel P s action t rule: lpp_ground_integer_no_step.induct)
 case (1 fuel P s action t)
 have included: "lpp_builtin_source P lpp_integer_no_builtin \<subseteq> lpp_builtin_source P lpp_ground_integer_no_builtin"
   by (rule lpp_builtin_source_mono) (auto simp: lpp_ground_integer_no_builtin_def)
 have prior: "lpp_integer_no_step fuel P s action t" using 1 by simp
 show ?case using included lpp_integer_no_step_sound[OF prior] by blast
next
 case (2 fuel P f a b gs es left right held t)
 obtain comparison reversed where name: "lpp_source_comparison f=Some (comparison,reversed)"
   and left_check: "lpp_expression_check [] left" and right_check: "lpp_expression_check [] right"
   and a: "a=lpp_expression_term left" and b: "b=lpp_expression_term right"
   and held: "held=lpp_integer_compare comparison
      (lpp_expression_value (if reversed then right else left) (\<lambda>_. 0))
      (lpp_expression_value (if reversed then left else right) (\<lambda>_. 0))"
   and t: "t=(if held then LPCGoals gs#es else es)"
   using 2 by (auto split: option.splits prod.splits)
 have descriptor: "lpp_comparison_descriptor f comparison reversed"
   using name lpp_source_comparison_descriptor by blast
 have ev_left: "lpp_integer_evaluation (lp_ieval a LPIVar) (lpp_expression_value left (\<lambda>_. 0))"
   unfolding a by (rule lpp_expression_evaluation[OF left_check]) simp
 have ev_right: "lpp_integer_evaluation (lp_ieval b LPIVar) (lpp_expression_value right (\<lambda>_. 0))"
   unfolding b by (rule lpp_expression_evaluation[OF right_check]) simp
 have outcome: "lpp_ground_integer_no_builtin f [lp_ieval a LPIVar,lp_ieval b LPIVar]
   (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
   using descriptor ev_left ev_right held
   by (cases reversed) (auto simp: lpp_ground_integer_no_builtin_def lpp_integer_compare_outcome_def)
 show ?case unfolding t
   by (rule lpp_ground_integer_comparison_step[OF lpp_comparison_selected[OF descriptor] outcome])
qed simp_all

definition lpp_ground_integer_no_check_source where
 "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps =
   lpp_builtin_trace_checker.check_source P (lpp_ground_integer_no_step fuel P) q modes argv a before after initial_steps steps"

theorem lpp_ground_integer_no_check_source_sound:
 assumes "lpp_ground_integer_no_check_source fuel P q modes argv a before after initial_steps steps"
 shows "length argv=length modes \<and>
   list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
   \<not> SN_on (lpp_builtin_source P lpp_ground_integer_no_builtin)
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 interpret trace: lpp_builtin_trace_checker P lpp_ground_integer_no_builtin "lpp_ground_integer_no_step fuel P"
   by unfold_locales (rule lpp_ground_integer_no_step_sound)
 show ?thesis using assms trace.check_source_sound
   by (simp add: lpp_ground_integer_no_check_source_def)
qed

ML \<open>
val checked = [@{thm lpp_ground_integer_no_check_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ground integer source-loop dependency" else ();
\<close>
end
