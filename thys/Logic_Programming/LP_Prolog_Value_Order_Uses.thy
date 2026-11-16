theory LP_Prolog_Value_Order_Uses
 imports LP_Prolog_Value_Return_Observations LP_Prolog_Success_Order_Rows
begin

definition lpp_value_order_use where
 "lpp_value_order_use value_table summaries ps use = (case use of (i,r) \<Rightarrow>
   if i<length ps \<and> r<length (summaries (fst (ps!i),length (snd (ps!i)))) then
    (case summaries (fst (ps!i),length (snd (ps!i)))!r of (increasing,selector,j) \<Rightarrow>
     if j<length (snd (ps!i)) then
      (case lpp_order_base_select lpp_integer_term (snd (ps!i)) selector of None \<Rightarrow> None
       | Some anchor \<Rightarrow> if anchor=lpp_integer_term (lpp_context_literal_candidate anchor) \<or>
          anchor\<in>set (concat (map (lpp_value_call_terms value_table) ps))
         then Some (increasing,anchor,snd (ps!i)!j) else None)
     else None) else None)"

lemma lpp_value_order_use_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and value_table: "lpp_check_value_program value_summaries P"
   and program: "lpp_check_order_program summaries P receipts"
   and selected: "lpp_value_order_use value_summaries summaries ps use=Some (increasing,anchor,t)"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
 shows "\<exists>n m. lpp_stable_scalar_evaluation operation (lp_ieval anchor eta) (lpp_integer_value n) \<and>
    lp_ieval t eta=lpp_integer_value m \<and> lpp_order_relation increasing n m"
proof -
 obtain i r j selector where index: "i<length ps"
   and rule_index: "r<length (summaries (fst (ps!i),length (snd (ps!i))))"
   and rule: "summaries (fst (ps!i),length (snd (ps!i)))!r=(increasing,selector,j)"
   and outterm: "t=snd (ps!i)!j" "j<length (snd (ps!i))"
   and anchor: "lpp_order_base_select lpp_integer_term (snd (ps!i)) selector=Some anchor"
   and typed: "anchor=lpp_integer_term (lpp_context_literal_candidate anchor) \<or>
     anchor\<in>set (concat (map (lpp_value_call_terms value_summaries) ps))"
   using selected by (auto simp: lpp_value_order_use_def split: prod.splits if_splits option.splits)
 have known: "\<exists>n. lpp_stable_scalar_evaluation operation (lp_ieval anchor eta) (lpp_integer_value n)"
 proof (cases "anchor=lpp_integer_term (lpp_context_literal_candidate anchor)")
   case True
   show ?thesis by (subst True, rule exI[of _ "lpp_context_literal_candidate anchor"])
     (simp add: lpp_stable_integer_literal)
 next
   case False
   obtain call_atom where member: "call_atom\<in>set ps"
     and argument: "anchor\<in>set (lpp_value_call_terms value_summaries call_atom)"
     using typed False by auto
   have actual: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval call_atom eta)"
     using helpers member by (simp add: list_all_iff)
   have summary: "lpp_value_summaries_hold (lpp_stable_scalar_evaluation operation) value_summaries (lpp_success_atom_eval call_atom eta)"
     by (rule lpp_check_value_program_sound[OF compatible value_table actual])
   show ?thesis by (rule lpp_value_call_terms_sound[OF summary argument])
 qed
 obtain n where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval anchor eta) (lpp_integer_value n)"
   using known by blast
 have actual: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval (ps!i) eta)"
   using helpers index by (simp add: list_all_length)
 have contracts: "lpp_order_summaries_hold operation summaries (lpp_success_atom_eval (ps!i) eta)"
   by (rule lpp_check_order_program_sound[OF compatible program actual])
 have contract: "lpp_order_contract_holds operation (map (\<lambda>t. lp_ieval t eta) (snd (ps!i))) (increasing,selector,j)"
   using contracts rule_index rule
   by (auto simp: lpp_order_summaries_hold_def lpp_success_atom_eval_def list_all_length)
 have selection: "lpp_order_base_select lpp_integer_value (map (\<lambda>t. lp_ieval t eta) (snd (ps!i))) selector=Some (lp_ieval anchor eta)"
   using lpp_order_base_select_map[of "\<lambda>t. lp_ieval t eta" lpp_integer_term "snd (ps!i)" selector] anchor
   by (simp add: o_def)
 show ?thesis using contract selection evaluated outterm
   by (auto simp: lpp_order_contract_holds_def)
qed


definition lpp_nonnegative_order_base where
 "lpp_nonnegative_order_base increasing anchor = (increasing \<and>
    anchor=lpp_integer_term (lpp_context_literal_candidate anchor) \<and>
    0\<le>lpp_context_literal_candidate anchor)"

lemma lpp_nonnegative_order_base_sound:
 assumes selected: "lpp_nonnegative_order_base increasing anchor"
   and evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval anchor eta) (lpp_integer_value n)"
   and ordered: "lpp_order_relation increasing n m"
 shows "0\<le>m"
proof -
 have shape: "increasing" "anchor=lpp_integer_term (lpp_context_literal_candidate anchor)"
   "0\<le>lpp_context_literal_candidate anchor"
   using selected by (simp_all add: lpp_nonnegative_order_base_def)
 have literal: "lpp_stable_scalar_evaluation operation (lp_ieval anchor eta)
      (lpp_integer_value (lpp_context_literal_candidate anchor))"
   by (subst shape(2)) (simp add: lpp_stable_integer_literal)
 have equal: "n=lpp_context_literal_candidate anchor"
   using lpp_stable_scalar_evaluation_unique[OF evaluated literal] by simp
 show ?thesis using ordered shape equal by (auto simp: lpp_order_relation_def)
qed

fun lpp_value_order_observations where
 "lpp_value_order_observations None = []"
| "lpp_value_order_observations (Some (increasing,anchor,t)) =
   [LPPOInteger t, if increasing then LPPOComparison LPPIntLessEqual anchor t
     else LPPOComparison LPPIntLessEqual t anchor] @
   (if lpp_nonnegative_order_base increasing anchor then [LPPOComparison LPPIntLessEqual (lpp_integer_term 0) t] else [])"

lemma lpp_evaluated_order_comparison:
 assumes compatible: "lpp_stable_integer_operations operation"
   and left: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
   and right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value m)"
   and ordered: "n\<le>m"
 shows "lpp_stable_compare_outcome operation LPPIntLessEqual a b (LPPBuiltinSuccess LPIVar)"
 by (rule lpp_evaluated_integer_comparison[OF compatible left right]) (use ordered in simp)

lemma lpp_value_order_observations_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and value_table: "lpp_check_value_program value_summaries P"
   and program: "lpp_check_order_program summaries P receipts"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
 shows "list_all (lpp_stable_observation_holds operation eta)
    (lpp_value_order_observations (lpp_value_order_use value_summaries summaries ps use))"
proof (cases "lpp_value_order_use value_summaries summaries ps use")
 case None then show ?thesis by simp
next
 case (Some selected)
 obtain increasing anchor t where shape: "selected=(increasing,anchor,t)" by (cases selected) auto
 obtain n m where evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval anchor eta) (lpp_integer_value n)"
   and literal: "lp_ieval t eta=lpp_integer_value m" and ordered: "lpp_order_relation increasing n m"
   using lpp_value_order_use_sound[OF compatible value_table program Some[unfolded shape] helpers] by blast
 show ?thesis using evaluated literal ordered lpp_nonnegative_order_base_sound[OF _ evaluated ordered]
   by (auto simp: Some shape lpp_order_relation_def lpp_is_integer_def
     intro: lpp_evaluated_order_comparison[OF compatible] lpp_stable_integer_literal)
qed

ML \<open>
val checked = [@{thm lpp_value_order_use_sound}, @{thm lpp_value_order_observations_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted evaluated-input return order dependency" else ();
\<close>
end
