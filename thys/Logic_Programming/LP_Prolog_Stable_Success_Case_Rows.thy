theory LP_Prolog_Stable_Success_Case_Rows
 imports LP_Prolog_Stable_Success_Case_Check
begin

fun lpp_success_case_output where
 "lpp_success_case_output source_row None = [source_row]"
| "lpp_success_case_output source_row (Some (i,k,children)) = children"

fun lpp_check_success_case_record where
 "lpp_check_success_case_record P source_row None = True"
| "lpp_check_success_case_record P source_row (Some (i,k,children)) =
    lpp_check_success_case_step P i k source_row children"

lemma lpp_check_success_case_record_sound:
 "lpp_check_success_case_record P source_row receipt \<Longrightarrow>
  lpp_stable_observed_calls operation {source_row} P \<subseteq>
   lpp_stable_observed_calls operation (set (lpp_success_case_output source_row receipt)) P"
 by (cases receipt) (auto split: prod.splits dest: lpp_check_success_case_step_sound[THEN subsetD])

lemma lpp_stable_observed_calls_union:
 "lpp_stable_observed_calls operation (A\<union>B) P =
  lpp_stable_observed_calls operation A P \<union> lpp_stable_observed_calls operation B P"
 by (unfold lpp_stable_observed_calls_def; blast)

lemma lpp_success_case_rows_sound:
 assumes "list_all2 (lpp_check_success_case_record P) source_rows receipts"
 shows "lpp_stable_observed_calls operation (set source_rows) P \<subseteq>
   lpp_stable_observed_calls operation (set (concat (map2 lpp_success_case_output source_rows receipts))) P"
 using assms
proof (induct rule: list_all2_induct)
 case Nil
 then show ?case by simp
next
 case (Cons source_row receipt source_rows receipts)
 have one: "lpp_stable_observed_calls operation {source_row} P \<subseteq>
   lpp_stable_observed_calls operation (set (lpp_success_case_output source_row receipt)) P"
   by (rule lpp_check_success_case_record_sound[OF Cons.hyps(1)])
 have source_union: "set (source_row#source_rows)={source_row}\<union>set source_rows" by simp
 have target_union: "set (concat (map2 lpp_success_case_output (source_row#source_rows) (receipt#receipts))) =
   set (lpp_success_case_output source_row receipt) \<union> set (concat (map2 lpp_success_case_output source_rows receipts))" by simp
 show ?case using one Cons.hyps(3)
   by (simp only: source_union target_union lpp_stable_observed_calls_union; blast)
qed

definition lpp_check_success_case_rows where
 "lpp_check_success_case_rows P source_rows receipts expanded =
   (list_all2 (lpp_check_success_case_record P) source_rows receipts \<and>
    expanded=concat (map2 lpp_success_case_output source_rows receipts))"

lemma lpp_check_success_case_rows_sound:
 "lpp_check_success_case_rows P source_rows receipts expanded \<Longrightarrow>
   lpp_stable_observed_calls operation (set source_rows) P \<subseteq>
   lpp_stable_observed_calls operation (set expanded) P"
 unfolding lpp_check_success_case_rows_def using lpp_success_case_rows_sound by blast

ML \<open>
val checked = [@{thm lpp_check_success_case_rows_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted successful-helper source_row coverage dependency" else ();
\<close>
end
