theory LP_Prolog_Success_Order_Rows
  imports LP_Prolog_Success_Order_Program LP_Prolog_Stable_Observed_Calls
begin

text \<open>Instantiate constant-base contracts only at actual successful prefix
calls. Every added integer fact and bound has a checked call and summary index.
The original guards, observations, endpoints and success program are retained.\<close>

definition lpp_order_use where
  "lpp_order_use summaries ps use = (case use of (i,r) \<Rightarrow>
    if i<length ps \<and> r<length (summaries (fst (ps!i),length (snd (ps!i)))) then
      (case summaries (fst (ps!i),length (snd (ps!i)))!r of
        (increasing,LPPOrderConstant k,j) \<Rightarrow>
          if j<length (snd (ps!i)) then Some (increasing,k,snd (ps!i)!j) else None
      | _ \<Rightarrow> None)
    else None)"

fun lpp_order_use_guards where
  "lpp_order_use_guards None = []"
| "lpp_order_use_guards (Some (increasing,k,t)) = [LPPSInteger t, LPPSOpaque
    (Fun (LPCUser ''2:=<'') (if increasing then [lpp_integer_term k,t] else [t,lpp_integer_term k]))]"

fun lpp_order_use_observations where
  "lpp_order_use_observations None = []"
| "lpp_order_use_observations (Some (increasing,k,t)) =
    [LPPOInteger t, (if increasing then LPPOComparison LPPIntLessEqual (lpp_integer_term k) t
      else LPPOComparison LPPIntLessEqual t (lpp_integer_term k))]"

lemma lpp_order_use_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_order_program summaries P receipts"
    and selected: "lpp_order_use summaries ps use=Some (increasing,k,t)"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
  shows "\<exists>m. lp_ieval t eta=lpp_integer_value m \<and> lpp_order_relation increasing k m"
proof -
  obtain i r j where index: "i<length ps"
    and rule_index: "r<length (summaries (fst (ps!i),length (snd (ps!i))))"
    and rule: "summaries (fst (ps!i),length (snd (ps!i)))!r=(increasing,LPPOrderConstant k,j)"
    and outterm: "t=snd (ps!i)!j" "j<length (snd (ps!i))"
    using selected by (auto simp: lpp_order_use_def split: prod.splits if_splits lpp_order_base.splits)
  have actual: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval (ps!i) eta)"
    using helpers index by (simp add: list_all_length)
  have contracts: "lpp_order_summaries_hold operation summaries (lpp_success_atom_eval (ps!i) eta)"
    by (rule lpp_check_order_program_sound[OF compatible program actual])
  have contract: "lpp_order_contract_holds operation (map (\<lambda>t. lp_ieval t eta) (snd (ps!i))) (increasing,LPPOrderConstant k,j)"
    using contracts rule_index rule
    by (auto simp: lpp_order_summaries_hold_def lpp_success_atom_eval_def list_all_length)
  show ?thesis using contract outterm lpp_stable_integer_literal[of operation k]
    by (auto simp: lpp_order_contract_holds_def)
qed

lemma lpp_order_integer_comparison:
  assumes compatible: "lpp_stable_integer_operations operation" and ordered: "n\<le>m"
  shows "lpp_stable_compare_outcome operation LPPIntLessEqual (lpp_integer_value n)
    (lpp_integer_value m) (LPPBuiltinSuccess LPIVar)"
  using ordered
  by (simp only: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
    lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal]) simp

lemma lpp_order_use_consequences:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_order_program summaries P receipts"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
  shows "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (lpp_order_use_guards (lpp_order_use summaries ps use)) \<and>
    list_all (lpp_stable_observation_holds operation eta)
      (lpp_order_use_observations (lpp_order_use summaries ps use))"
proof (cases "lpp_order_use summaries ps use")
  case None then show ?thesis by simp
next
  case (Some selected)
  obtain increasing k t where shape: "selected=(increasing,k,t)" by (cases selected) auto
  obtain m where integer: "lp_ieval t eta=lpp_integer_value m"
    and ordered: "lpp_order_relation increasing k m"
    using lpp_order_use_sound[OF compatible program Some[unfolded shape] helpers] by blast
  show ?thesis using ordered
    by (auto simp: Some shape integer lpp_is_integer_def lpp_order_relation_def
      intro: lpp_order_integer_comparison[OF compatible])
qed

definition lpp_order_insert where
  "lpp_order_insert insert_at original added = (case insert_at of None \<Rightarrow> original@added
    | Some n \<Rightarrow> take n original @ added @ drop n original)"

lemma lpp_order_insert_set:
  "set (lpp_order_insert insert_at original added) = set original \<union> set added"
proof (cases insert_at)
  case None then show ?thesis by (simp add: lpp_order_insert_def)
next
  case (Some n)
  have parts: "set (take n original) \<union> set (drop n original) = set original"
    by (metis append_take_drop_id set_append)
  show ?thesis using parts
    by (simp add: lpp_order_insert_def Some Un_assoc Un_left_commute Un_commute)
qed

lemma lpp_order_insert_all[simp]:
  "list_all P (lpp_order_insert insert_at original added) = (list_all P original \<and> list_all P added)"
  by (auto simp: list_all_iff lpp_order_insert_set)

definition lpp_enrich_order_row where
  "lpp_enrich_order_row summaries selection source_row = (case source_row of ((h,ps,b,gs),os) \<Rightarrow>
    ((h,ps,b,gs@concat (map (\<lambda>u. lpp_order_use_guards (lpp_order_use summaries ps u)) (snd selection))),
       lpp_order_insert (fst selection) os (concat (map (\<lambda>u. lpp_order_use_observations (lpp_order_use summaries ps u)) (snd selection)))))"

definition lpp_enrich_order_rows where
  "lpp_enrich_order_rows summaries uses D = map (\<lambda>i. lpp_enrich_order_row summaries (uses!i) (D!i)) [0..<length D]"

lemma lpp_enriched_order_calls:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_order_program summaries P receipts"
    and count: "length uses=length D"
  shows "lpp_stable_observed_calls operation (set D) P \<subseteq>
    lpp_stable_observed_calls operation (set (lpp_enrich_order_rows summaries uses D)) P"
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
  have enriched: "lpp_enrich_order_row summaries (uses!i) ((h,ps,b,gs),os)\<in>
      set (lpp_enrich_order_rows summaries uses D)"
    using index original by (force simp: lpp_enrich_order_rows_def)
  have consequences: "\<And>use. list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (lpp_order_use_guards (lpp_order_use summaries ps use)) \<and>
    list_all (lpp_stable_observation_holds operation eta)
      (lpp_order_use_observations (lpp_order_use summaries ps use))"
    by (rule lpp_order_use_consequences[OF compatible program helpers])
  let ?gs = "gs@concat (map (\<lambda>u. lpp_order_use_guards (lpp_order_use summaries ps u)) (snd (uses!i)))"
  let ?os = "lpp_order_insert (fst (uses!i)) os (concat (map (\<lambda>u. lpp_order_use_observations (lpp_order_use summaries ps u)) (snd (uses!i))))"
  have enriched_row: "((h,ps,b,?gs),?os)\<in>set (lpp_enrich_order_rows summaries uses D)"
    using enriched by (simp add: lpp_enrich_order_row_def)
  have enriched_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) ?gs"
    using guards consequences by (auto simp: list_all_iff)
  have enriched_observations: "list_all (lpp_stable_observation_holds operation eta) ?os"
    using observations consequences by (auto simp: list_all_iff lpp_order_insert_set)
  show "edge\<in>lpp_stable_observed_calls operation (set (lpp_enrich_order_rows summaries uses D)) P"
    unfolding edge lpp_stable_observed_calls_def
    apply (rule CollectI)
    apply (rule exI[of _ a], rule exI[of _ h], rule exI[of _ ps], rule exI[of _ b],
      rule exI[of _ ?gs], rule exI[of _ ?os], rule exI[of _ sigma], rule exI[of _ eta])
    using enriched_row matching enriched_guards enriched_observations helpers by simp
qed

theorem lpp_enriched_order_calls_SN:
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_order_program summaries P receipts"
    and count: "length uses=length D"
    and child: "SN (lpp_stable_observed_calls operation (set (lpp_enrich_order_rows summaries uses D)) P)"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
  by (rule SN_subset[OF child lpp_enriched_order_calls[OF compatible program count]])

ML \<open>
val checked = [@{thm lpp_enriched_order_calls_SN}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted actual-return enrichment dependency" else ();
\<close>
end
