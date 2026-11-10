theory LP_Prolog_Stable_Shape_Coverage
 imports LP_Prolog_Stable_Shape_Entries LP_Prolog_Stable_Structural_Child
begin

fun lpp_check_shape_coverage_row where
  "lpp_check_shape_coverage_row T entries flt p d marks ((h,ps,b,gs),os)
      (slot,facts,G,seeds,shapes) =
    (slot<length entries \<and> (case entries!slot of (q,n,positions) \<Rightarrow>
      fst b=q \<and> length (snd b)=n \<and>
      lp_check_query flt (the_default (p (LPCUser q)) (map_of marks (p (LPCUser q)))) n positions \<and>
      lp_return_shape_filter_check flt d G \<and>
      lpp_check_shape_entry_row T G seeds shapes positions ((h,ps,b,gs),os) facts))"

definition lpp_check_shape_coverage where
  "lpp_check_shape_coverage T entries flt p d marks D evidence =
    (length evidence=length D \<and> list_all (\<lambda>i.
      lpp_check_shape_coverage_row T entries flt p d marks (D!i) (evidence!i)) [0..<length D])"

lemma lpp_checked_shape_row_termination:
  fixes P :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_shape_coverage_row T entries flt p d marks ((h,ps,b,gs),os) evidence"
    and transfer: "lpp_check_transfer_program T P receipts"
    and observed: "lpp_stable_context_holds operation P (ps,gs,os) eta"
    and filter: "afs_of filters=Some flt"
    and children: "lpp_check_structural_pidp_entries I J child_rows (lpp_erase_success P) entries
      p d outs fallback dnames pnames marks filters labs proofs"
  shows "SN_on (lp_triple_calls (set child_rows) (lpp_erase_success P)) {lpp_lift_iatom (lpp_success_atom_eval b eta)}"
proof -
  obtain slot facts G seeds shapes where evidence: "evidence=(slot,facts,G,seeds,shapes)"
    by (cases evidence) auto
  obtain q n positions where entry: "entries!slot=(q,n,positions)" by (cases "entries!slot") auto
  have slot: "slot<length entries" and name: "fst b=q" and len: "length (snd b)=n"
    and query: "lp_check_query flt (the_default (p (LPCUser q)) (map_of marks (p (LPCUser q)))) n positions"
    and shape_filter: "lp_return_shape_filter_check flt d G"
    and row: "lpp_check_shape_entry_row T G seeds shapes positions ((h,ps,b,gs),os) facts"
    using checked by (auto simp only: evidence lpp_check_shape_coverage_row.simps entry case_prod_conv)
  have member: "(q,n,positions)\<in>set entries" using nth_mem[OF slot] entry by simp
  have child: "check_lp_triple_pidp I J (lp_roles_triples p d child_rows)
      (lp_roles_program p d (lpp_erase_success P)) outs fallback dnames pnames marks filters
      (p (LPCUser q)) n positions labs proofs"
    using children member by (auto simp: lpp_check_structural_pidp_entries_def list_all_iff)
  have arguments: "\<forall>i\<in>set positions. i<length (snd b) \<and>
      (\<exists>u::((string,nat list) lab,string) term. lp_iproject flt (map_lp_iterm d id (snd (lpp_success_atom_eval b eta)!i)) u)"
    by (rule lpp_checked_shape_entry_projections[OF compatible row transfer observed shape_filter])
  have runtime_length: "length (snd (lpp_success_atom_eval b eta))=n"
    using len by (simp add: lpp_success_atom_eval_def)
  have projection: "\<exists>u::((string,nat list) lab,string) term.
    lp_iproject flt (LPIFun (the_default (p (LPCUser q)) (map_of marks (p (LPCUser q))))
      (map (map_lp_iterm d id) (snd (lpp_success_atom_eval b eta)))) u"
    by (rule lp_check_query_projectable[OF query runtime_length]) (use arguments in blast)
  obtain u::"((string,nat list) lab,string) term" where projected:
    "lp_iproject flt (LPIFun (the_default (p (LPCUser q)) (map_of marks (p (LPCUser q))))
      (map (map_lp_iterm d id) (snd (lpp_success_atom_eval b eta)))) u"
    using projection by blast
  have result: "SN_on (lp_triple_calls (set child_rows) (lpp_erase_success P))
      {(LPCUser q,snd (lpp_success_atom_eval b eta))}"
    by (rule check_lp_triple_pidp_projected_roles_sound[OF I J child filter projected])
  show ?thesis using result name by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def)
qed

theorem lpp_checked_shape_pidp_component:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and coverage: "lpp_check_shape_coverage T entries flt p d marks D evidence"
    and transfer: "lpp_check_transfer_program T P receipts"
    and subject: "set child_rows=lpp_erase_triples (fst ` set D)"
    and filter: "afs_of filters=Some flt"
    and children: "lpp_check_structural_pidp_entries I J child_rows (lpp_erase_success P) entries
      p d outs fallback dnames pnames marks filters labs proofs"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof -
  let ?S = "lp_triple_calls (set child_rows) (lpp_erase_success P)"
  have targets: "SN_on ?S {lpp_lift_iatom b}"
    if edge: "(a,b)\<in>(lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)" for a b
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
    have all_rows: "\<forall>j\<in>set [0..<length D]. lpp_check_shape_coverage_row T entries flt p d marks (D!j) (evidence!j)"
      using coverage by (simp only: lpp_check_shape_coverage_def list_all_iff) blast
    have at: "lpp_check_shape_coverage_row T entries flt p d marks (D!i) (evidence!i)"
      by (rule bspec[OF all_rows]) (use index in simp)
    have local: "lpp_check_shape_coverage_row T entries flt p d marks ((h,ps,target,gs),os) (evidence!i)"
      using at by (simp only: row)
    have observed: "lpp_stable_context_holds operation P (ps,gs,os) eta"
      using guards observations prefix by (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff dest: lpp_stable_observation_refines)
    show ?thesis unfolding result
      by (rule lpp_checked_shape_row_termination[OF I J compatible local transfer observed filter children])
  qed
  show ?thesis
    apply (rule lpp_typed_relational_simulation_SN[where
      T="\<lambda>b. SN_on ?S {lpp_lift_iatom b}" and rep="\<lambda>b s. s=lpp_lift_iatom b" and S="?S"])
    apply (erule targets)
    apply blast
    unfolding subject by (blast dest: lpp_stable_call_structural)
qed

ML \<open>
val checked = [@{thm lpp_checked_shape_pidp_component}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted shape component" else ();
\<close>

end
