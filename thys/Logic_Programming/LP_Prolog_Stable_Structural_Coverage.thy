theory LP_Prolog_Stable_Structural_Coverage
 imports LP_Prolog_Stable_Structural_Entries
begin

fun lpp_check_structural_entry_row where
  "lpp_check_structural_entry_row T entries ((h,ps,b,gs),os) (slot,facts) =
    (slot<length entries \<and>
      (case entries!slot of (q,n,positions) \<Rightarrow>
        fst b=q \<and> length (snd b)=n \<and>
        lpp_check_stable_structural_selected_row T ((h,ps,b,gs),os) positions facts))"

definition lpp_check_structural_entry_coverage where
  "lpp_check_structural_entry_coverage T entries D evidence =
    (length evidence=length D \<and>
      list_all (\<lambda>i. lpp_check_structural_entry_row T entries (D!i) (evidence!i)) [0..<length D])"

lemma lpp_checked_structural_entry_target:
  fixes P :: "'v lpp_success_clause list"
    and evidence :: "nat * 'v lpp_transfer_fact list"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_structural_entry_row T entries ((h,ps,b,gs),os) evidence"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
  shows "lpp_structural_entry_admissible entries (lpp_success_atom_eval b eta)"
proof -
  obtain slot facts where evidence: "evidence=(slot,facts)" by (cases evidence) auto
  obtain q n positions where entry_shape: "entries!slot=(q,n,positions)"
    by (cases "entries!slot") auto
  have slot: "slot<length entries" and name: "fst b=q" and len: "length (snd b)=n"
    and row: "lpp_check_stable_structural_selected_row T ((h,ps,b,gs),os) positions facts"
    using checked by (simp_all add: evidence entry_shape)
  have member: "(q,n,positions)\<in>set entries" using nth_mem[OF slot] entry_shape by simp
  have finite: "\<forall>i\<in>set positions. i<length (snd b) \<and> lp_seg_ground (snd (lpp_success_atom_eval b eta)!i)"
    by (rule lpp_stable_structural_selected_target[OF compatible row transfer guards prefix observations])
  have signature: "fst (lpp_success_atom_eval b eta)=q" "length (snd (lpp_success_atom_eval b eta))=n"
    using name len by (simp_all add: lpp_success_atom_eval_def)
  have finite_entry: "\<forall>i\<in>set positions. i<n \<and> lp_seg_ground (snd (lpp_success_atom_eval b eta)!i)"
    using finite by (simp only: len)
  show ?thesis
    unfolding lpp_structural_entry_admissible_def
    by (rule exI[of _ q], rule exI[of _ n], rule exI[of _ positions])
      (rule conjI[OF member conjI[OF signature(1) conjI[OF signature(2) finite_entry]]])
qed

lemma lpp_checked_structural_coverage_target:
  fixes P :: "'v lpp_success_clause list" and D :: "'v lpp_observed_triple list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_structural_entry_coverage T entries D evidence"
    and transfer: "lpp_check_transfer_program T P receipts"
    and edge: "(a,b)\<in>lpp_stable_observed_calls operation (set D) P"
  shows "lpp_structural_entry_admissible entries b"
proof -
  obtain h ps target gs os sigma eta where member: "((h,ps,target,gs),os)\<in>set D"
    and result: "b=lpp_success_atom_eval target eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observations: "list_all (lpp_stable_observation_holds operation eta) os"
    and prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using edge by (auto simp: lpp_stable_observed_calls_def)
  obtain i where index: "i<length D" and row: "D!i=((h,ps,target,gs),os)"
    using member by (auto simp: in_set_conv_nth)
  have all_rows: "\<forall>j\<in>set [0..<length D]. lpp_check_structural_entry_row T entries (D!j) (evidence!j)"
    using checked by (simp only: lpp_check_structural_entry_coverage_def list_all_iff) blast
  have at: "lpp_check_structural_entry_row T entries (D!i) (evidence!i)"
    by (rule bspec[OF all_rows]) (use index in simp)
  have local: "lpp_check_structural_entry_row T entries ((h,ps,target,gs),os) (evidence!i)"
    using at by (simp only: row)
  show ?thesis unfolding result
    by (rule lpp_checked_structural_entry_target[OF compatible local transfer guards prefix observations])
qed

ML \<open>
val checked = [@{thm lpp_checked_structural_entry_target}, @{thm lpp_checked_structural_coverage_target}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted structural row coverage" else ();
\<close>
end
