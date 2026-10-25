theory LP_Cut_SEG_Triple_Proofs
  imports LP_Cut_SEG_Triple_Control LP_Cut_SEG_Triple_Labels
    LP_Cut_SEG_Triple_XML LP_Cut_SEG_Triple_Receipt_Test
begin

text \<open>Proof audit for the complete source-bound SEG/triples connection,
including executable boundary and successful-return receipts, recursive Split,
original query modes and the Pi-DP certificate endpoint.\<close>

ML \<open>
val audited = [@{thm lpc_return_contract_separate_descent},
  @{thm lpc_return_split_separate_descent}, @{thm lpc_triples_source_contract},
  @{thm lpc_seg_triple_control_contract}, @{thm lpc_seg_template_path_instance},
  @{thm lpc_seg_template_path_triple_edge}, @{thm lpc_triple_success_clause_answers},
  @{thm check_lpc_seg_triples_sound}, @{thm check_lpc_seg_triples_xml_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted SEG/triples source-connection dependency" else ();
val _ = writeln "SEG/TRIPLES: full source-bound certificate chain audited";
\<close>

end
