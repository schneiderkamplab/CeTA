theory LP_Prolog_Value_Order_Rows
 imports LP_Prolog_Value_Order_Uses
begin

fun lpp_value_order_guards where
 "lpp_value_order_guards None = []"
| "lpp_value_order_guards (Some (increasing,anchor,t)) =
   [LPPSInteger t, LPPSOpaque (Fun (LPCUser ''2:=<'') (if increasing then [anchor,t] else [t,anchor]))] @
   (if lpp_nonnegative_order_base increasing anchor then [LPPSOpaque (Fun (LPCUser ''2:=<'') [lpp_integer_term 0,t])] else [])"

definition lpp_value_return_guard where
 "lpp_value_return_guard t = LPPSOpaque (Fun (LPCUser ''2:=:='')
   [Fun (LPCUser ''2:prolog_data_6d6f64'') [t,lpp_integer_term 1],lpp_integer_term 0])"

definition lpp_value_order_additions where
 "lpp_value_order_additions value_table summaries ps return_terms order_uses =
   (map lpp_value_return_guard return_terms @ concat (map (\<lambda>u. lpp_value_order_guards
       (lpp_value_order_use value_table summaries ps u)) order_uses),
    map lpp_value_observation return_terms @ concat (map (\<lambda>u. lpp_value_order_observations
       (lpp_value_order_use value_table summaries ps u)) order_uses))"

lemma lpp_value_order_additions_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and value_table: "lpp_check_value_program value_summaries P"
   and program: "lpp_check_order_program summaries P receipts"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
   and return_terms: "set ts \<subseteq> set (concat (map (lpp_value_call_terms value_summaries) ps))"
 shows "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
     (fst (lpp_value_order_additions value_summaries summaries ps ts order_uses)) \<and>
   list_all (lpp_stable_observation_holds operation eta)
     (snd (lpp_value_order_additions value_summaries summaries ps ts order_uses))"
proof -
 have observations: "list_all (lpp_stable_observation_holds operation eta) (map lpp_value_observation ts)"
   using lpp_value_return_observations_sound[OF compatible value_table helpers] return_terms
   by (auto simp: lpp_value_return_observations_def list_all_iff)
 have orders: "list_all (lpp_stable_observation_holds operation eta)
    (lpp_value_order_observations (lpp_value_order_use value_summaries summaries ps u))" for u
   by (rule lpp_value_order_observations_sound[OF compatible value_table program helpers])
 have guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
    (lpp_value_order_guards (lpp_value_order_use value_summaries summaries ps u))" for u
   using orders[of u]
   by (cases "lpp_value_order_use value_summaries summaries ps u") auto
 show ?thesis using observations orders guards
   by (auto simp: lpp_value_order_additions_def lpp_value_return_guard_def list_all_iff)
qed

definition lpp_check_value_order_selection where
 "lpp_check_value_order_selection value_table summaries source_row selection =
   (case (source_row,selection) of (((h,ps,b,gs),os),(insert_at,return_terms,order_uses)) \<Rightarrow>
    set return_terms \<subseteq> set (concat (map (lpp_value_call_terms value_table) ps)) \<and>
    list_all (\<lambda>u. lpp_value_order_use value_table summaries ps u\<noteq>None) order_uses \<and>
    (case insert_at of None \<Rightarrow> True | Some n \<Rightarrow> n\<le>length os))"

definition lpp_enrich_value_order_row where
 "lpp_enrich_value_order_row value_table summaries selection source_row =
   (case (source_row,selection) of (((h,ps,b,gs),os),(insert_at,return_terms,order_uses)) \<Rightarrow>
     (let added=lpp_value_order_additions value_table summaries ps return_terms order_uses in
      ((h,ps,b,gs@fst added),lpp_order_insert insert_at os (snd added))))"

definition lpp_enrich_value_order_rows where
 "lpp_enrich_value_order_rows value_table summaries selections D =
    map (\<lambda>i. lpp_enrich_value_order_row value_table summaries (selections!i) (D!i)) [0..<length D]"

lemma lpp_enriched_value_order_calls:
 assumes compatible: "lpp_stable_integer_operations operation"
   and value_table: "lpp_check_value_program value_summaries P"
   and program: "lpp_check_order_program summaries P receipts"
   and count: "length selections=length D"
   and checked: "list_all (\<lambda>i. lpp_check_value_order_selection value_summaries summaries (D!i) (selections!i)) [0..<length D]"
 shows "lpp_stable_observed_calls operation (set D) P  \<subseteq> 
   lpp_stable_observed_calls operation (set (lpp_enrich_value_order_rows value_summaries summaries selections D)) P"
proof
 fix edge assume member: "edge\<in>lpp_stable_observed_calls operation (set D) P"
 obtain a h ps b gs os sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
   and source_row: "((h,ps,b,gs),os)\<in>set D"
   and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
   and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
   and observations: "list_all (lpp_stable_observation_holds operation eta) os"
   and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
     (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
   using member by (auto simp: lpp_stable_observed_calls_def)
 obtain i where index: "i<length D" and original: "D!i=((h,ps,b,gs),os)"
   using source_row by (auto simp: in_set_conv_nth)
 obtain insert_at return_terms order_uses where selection: "selections!i=(insert_at,return_terms,order_uses)" by (cases "selections!i") auto
 have selected_check: "lpp_check_value_order_selection value_summaries summaries (D!i) (selections!i)"
   using checked index by (simp add: list_all_iff)
 have return_terms: "set return_terms \<subseteq> set (concat (map (lpp_value_call_terms value_summaries) ps))"
   using selected_check by (simp add: original selection lpp_check_value_order_selection_def)
 let ?added = "lpp_value_order_additions value_summaries summaries ps return_terms order_uses"
 have consequences: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) (fst ?added) \<and>
   list_all (lpp_stable_observation_holds operation eta) (snd ?added)"
   by (rule lpp_value_order_additions_sound[OF compatible value_table program helpers return_terms])
 have enriched: "((h,ps,b,gs@fst ?added),lpp_order_insert insert_at os (snd ?added))\<in>
     set (lpp_enrich_value_order_rows value_summaries summaries selections D)"
   using index original selection
   by (force simp: lpp_enrich_value_order_rows_def lpp_enrich_value_order_row_def Let_def)
 show "edge\<in>lpp_stable_observed_calls operation (set (lpp_enrich_value_order_rows value_summaries summaries selections D)) P"
   unfolding edge lpp_stable_observed_calls_def
   apply (rule CollectI)
   apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ b],
     rule exI[of _ "gs@fst ?added"], rule exI[of _ "lpp_order_insert insert_at os (snd ?added)"],
     rule exI[of _ sigma], rule exI[of _ eta])
   using enriched matching guards observations helpers consequences by simp
qed

ML \<open>
val checked = [@{thm lpp_enriched_value_order_calls}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted value-order row dependency" else ();
\<close>
end
