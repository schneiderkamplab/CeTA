theory LP_Prolog_Success_Magnitude_Program
 imports LP_Prolog_Success_Magnitude_Facts
begin

definition lpp_check_magnitude_clause where
  "lpp_check_magnitude_clause summaries c j receipt = (case c of (h,bs,gs) \<Rightarrow>
    let known=lpp_magnitude_inputs j (snd h); fs=fst receipt in
      j<length (snd h) \<and> lpp_check_magnitude_facts summaries bs gs known fs \<and>
      lpp_check_magnitude_bound (known@map lpp_magnitude_conclusion fs) (snd h!j) (snd receipt))"

lemma lpp_check_magnitude_clause_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_magnitude_clause summaries (h,bs,gs) j receipt"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_magnitude_holds operation summaries (lpp_success_atom_eval b eta)) bs"
  shows "j<length (snd (lpp_success_atom_eval h eta)) \<and>
    abs (lpp_stable_scaled_bound operation (snd (lpp_success_atom_eval h eta)!j)) \<le>
      lpp_magnitude_max operation (lpp_magnitude_inputs j (snd (lpp_success_atom_eval h eta)))"
proof -
  let ?known = "lpp_magnitude_inputs j (snd h)"
  let ?values = "map (\<lambda>t. lp_ieval t eta) ?known"
  let ?M = "lpp_magnitude_max operation ?values"
  have index: "j<length (snd h)"
    and facts: "lpp_check_magnitude_facts summaries bs gs ?known (fst receipt)"
    and bound: "lpp_check_magnitude_bound (?known@map lpp_magnitude_conclusion (fst receipt)) (snd h!j) (snd receipt)"
    using checked by (auto simp: lpp_check_magnitude_clause_def Let_def)
  have nonnegative: "0\<le>?M" by (rule lpp_magnitude_max_nonnegative)
  have known: "abs (lpp_stable_scaled_bound operation (lp_ieval t eta))\<le>?M"
    if "t\<in>set ?known" for t
    by (rule lpp_magnitude_max_upper) (use that in auto)
  have complete: "abs (lpp_stable_scaled_bound operation (lp_ieval t eta))\<le>?M"
    if "t\<in>set (?known@map lpp_magnitude_conclusion (fst receipt))" for t
    by (rule lpp_check_magnitude_facts_sound[OF compatible facts known nonnegative guards helpers that])
  have result: "abs (lpp_stable_scaled_bound operation (lp_ieval (snd h!j) eta))\<le>?M"
    by (rule lpp_check_magnitude_bound_sound[OF compatible bound complete nonnegative])
  show ?thesis using index result
    by (simp add: lpp_success_atom_eval_def lpp_magnitude_inputs_map)
qed

definition lpp_check_magnitude_rows where
  "lpp_check_magnitude_rows summaries c receipts = (case c of (h,bs,gs) \<Rightarrow>
    list_all2 (lpp_check_magnitude_clause summaries c) (summaries (fst h,length (snd h))) receipts)"

definition lpp_check_magnitude_program where
  "lpp_check_magnitude_program summaries P receipts =
    list_all2 (lpp_check_magnitude_rows summaries) P receipts"

theorem lpp_check_magnitude_program_sound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_magnitude_program summaries P receipts"
    and success: "lpp_guarded_success P (lpp_stable_scalar_evaluation operation) a"
  shows "lpp_magnitude_holds operation summaries a"
proof (rule lpp_magnitude_success_invariant[OF success])
  fix h bs gs eta
  assume member: "(h,bs,gs)\<in>set P"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_magnitude_holds operation summaries (lpp_success_atom_eval b eta)) bs"
  obtain rows_receipt where row: "lpp_check_magnitude_rows summaries (h,bs,gs) rows_receipt"
    using lpp_magnitude_list_all2_member[OF checked[unfolded lpp_check_magnitude_program_def] member] by blast
  have result: "j<length (snd (lpp_success_atom_eval h eta)) \<and>
      abs (lpp_stable_scaled_bound operation (snd (lpp_success_atom_eval h eta)!j)) \<le>
        lpp_magnitude_max operation (lpp_magnitude_inputs j (snd (lpp_success_atom_eval h eta)))"
    if selected: "j\<in>set (summaries (fst h,length (snd h)))" for j
  proof -
    obtain receipt where clause: "lpp_check_magnitude_clause summaries (h,bs,gs) j receipt"
      using lpp_magnitude_list_all2_member[OF row[unfolded lpp_check_magnitude_rows_def, simplified] selected] by blast
    show ?thesis by (rule lpp_check_magnitude_clause_sound[OF compatible clause guards helpers])
  qed
  show "lpp_magnitude_holds operation summaries (lpp_success_atom_eval h eta)"
    unfolding lpp_magnitude_holds_def
  proof (intro ballI)
    fix j assume selected: "j\<in>set (summaries (fst (lpp_success_atom_eval h eta),length (snd (lpp_success_atom_eval h eta))))"
    have original: "j\<in>set (summaries (fst h,length (snd h)))"
      using selected by (simp add: lpp_success_atom_eval_def)
    show "j<length (snd (lpp_success_atom_eval h eta)) \<and>
      abs (lpp_stable_scaled_bound operation (snd (lpp_success_atom_eval h eta)!j)) \<le>
        lpp_magnitude_max operation (lpp_magnitude_inputs j (snd (lpp_success_atom_eval h eta)))"
      by (rule result[OF original])
  qed
qed

ML \<open>
val checked = [@{thm lpp_check_magnitude_program_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude program dependency" else ();
\<close>
end
