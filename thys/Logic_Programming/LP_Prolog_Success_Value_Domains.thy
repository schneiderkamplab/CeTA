theory LP_Prolog_Success_Value_Domains
 imports LP_Prolog_Numeric_Return_Calls
begin

text \<open>These summaries concern finite successful derivations, not helper
termination. An argument can be an expression whose value is an integer without
being a literal integer term. Every defining clause is checked.\<close>

definition lpp_value_positions where
 "lpp_value_positions E positions ts = list_all (\<lambda>i. i<length ts \<and>
    (\<exists>n. E (ts!i) (lpp_integer_value n))) positions"

definition lpp_value_summaries_hold where
 "lpp_value_summaries_hold E summaries a = lpp_value_positions E (summaries (fst a,length (snd a))) (snd a)"

definition lpp_value_call_terms where
 "lpp_value_call_terms summaries b = map (\<lambda>i. snd b!i)
    (filter (\<lambda>i. i<length (snd b)) (summaries (fst b,length (snd b))))"

lemma lpp_value_call_terms_sound:
 assumes summary: "lpp_value_summaries_hold E summaries (lpp_success_atom_eval b eta)"
   and member: "t\<in>set (lpp_value_call_terms summaries b)"
 shows "\<exists>n. E (lp_ieval t eta) (lpp_integer_value n)"
proof -
 obtain i where selected: "i\<in>set (summaries (fst b,length (snd b)))"
   and index: "i<length (snd b)" and selected_term: "t=snd b!i"
   using member by (auto simp: lpp_value_call_terms_def)
 have all: "\<forall>j\<in>set (summaries (fst b,length (snd b))). j<length (snd b) \<and>
    (\<exists>n. E (map (\<lambda>t. lp_ieval t eta) (snd b)!j) (lpp_integer_value n))"
   using summary unfolding lpp_value_summaries_hold_def lpp_value_positions_def
     lpp_success_atom_eval_def by (simp only: fst_conv snd_conv length_map list_all_iff)
 have chosen: "i<length (snd b) \<and> (\<exists>n. E (map (\<lambda>t. lp_ieval t eta) (snd b)!i) (lpp_integer_value n))"
   by (rule all[rule_format, OF selected])
 show ?thesis using chosen index by (simp add: selected_term)
qed

definition lpp_value_clause_known where
 "lpp_value_clause_known P summaries bs gs =
   concat (map lpp_success_evaluated_integers (lpp_numeric_enriched_guards P bs gs)) @
   concat (map (lpp_value_call_terms summaries) bs)"

definition lpp_check_value_clause where
 "lpp_check_value_clause P summaries c = (case c of (h,bs,gs) \<Rightarrow>
    list_all (\<lambda>i. i<length (snd h) \<and>
      (snd h!i\<in>set (lpp_value_clause_known P summaries bs gs) \<or>
       snd h!i=lpp_integer_term (lpp_context_literal_candidate (snd h!i)))) (summaries (fst h,length (snd h))))"

definition lpp_check_value_program where
 "lpp_check_value_program summaries P = list_all (lpp_check_value_clause P summaries) P"

theorem lpp_check_value_program_sound:
 assumes compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_value_program summaries P"
   and success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) a"
 shows "lpp_value_summaries_hold (lpp_stable_scalar_evaluation operation) summaries a"
proof (rule lpp_success_invariant_with_calls[OF success])
 fix h bs gs eta
 assume member: "(h,bs,gs)\<in>set P"
   and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
   and actual: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>b. lpp_success_atom_eval b eta) bs)"
   and helpers: "list_all (\<lambda>b. lpp_value_summaries_hold (lpp_stable_scalar_evaluation operation)
      summaries (lpp_success_atom_eval b eta)) bs"
 have clause: "lpp_check_value_clause P summaries (h,bs,gs)"
   using checked member by (simp add: lpp_check_value_program_def list_all_iff)
 have enriched: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
     (lpp_numeric_enriched_guards P bs gs)"
   by (rule lpp_numeric_enriched_guards_sound[OF guards actual])
 have known: "\<exists>n. lpp_stable_scalar_evaluation operation (lp_ieval t eta) (lpp_integer_value n)"
   if "t\<in>set (lpp_value_clause_known P summaries bs gs)" for t
   using that enriched helpers
   by (auto simp: lpp_value_clause_known_def list_all_iff
     intro: lpp_success_evaluated_integers_sound[OF compatible] lpp_value_call_terms_sound)
 have outputs: "i<length (snd h) \<and> (\<exists>n. lpp_stable_scalar_evaluation operation
       (lp_ieval (snd h!i) eta) (lpp_integer_value n))"
   if selected: "i\<in>set (summaries (fst h,length (snd h)))" for i
 proof -
   have all: "\<forall>j\<in>set (summaries (fst h,length (snd h))). j<length (snd h) \<and>
     (snd h!j\<in>set (lpp_value_clause_known P summaries bs gs) \<or>
       snd h!j=lpp_integer_term (lpp_context_literal_candidate (snd h!j)))"
     using clause by (simp only: lpp_check_value_clause_def split_conv list_all_iff)
   have chosen: "i<length (snd h) \<and>
     (snd h!i\<in>set (lpp_value_clause_known P summaries bs gs) \<or>
       snd h!i=lpp_integer_term (lpp_context_literal_candidate (snd h!i)))"
     by (rule all[rule_format, OF selected])
   have literal: "\<exists>n. lpp_stable_scalar_evaluation operation
      (lp_ieval (lpp_integer_term k) eta) (lpp_integer_value n)" for k
     by (rule exI[of _ k]) (simp add: lpp_stable_integer_literal)
   show ?thesis using chosen known literal by metis
 qed
 show "lpp_value_summaries_hold (lpp_stable_scalar_evaluation operation) summaries (lpp_success_atom_eval h eta)"
   using outputs by (auto simp: lpp_value_summaries_hold_def lpp_value_positions_def
     lpp_success_atom_eval_def list_all_iff)
qed

ML \<open>
val checked = [@{thm lpp_check_value_program_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted actual-return evaluated value dependency" else ();
\<close>
end
