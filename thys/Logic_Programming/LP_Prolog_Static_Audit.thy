theory LP_Prolog_Static_Audit
  imports LP_Prolog_Undefined_XML LP_Prolog_Graph_Projection LP_Prolog_Answers
begin
ML \<open>
val audited = [@{thm lpp_return_graph_contract}, @{thm lpp_answer_instrumentation_SN}, @{thm lpp_atomic_uncaught_errors}, @{thm lpc_return_graph_contract}, @{thm lpp_graph_equations_solution}, @{thm lpp_check_graph_projection_sound}, @{thm check_lpp_undefined_xml_sound}, @{thm check_lpc_uniform_xml_sound}, @{thm check_lpp_uniform_xml_sound},
  @{thm check_lpp_static_no_xml_sound}, @{thm lp_prolog_static_nontermination},
  @{thm check_lpp_static_xml_sound},
  @{thm lp_prolog_static_termination}, @{thm lp_prolog_uncaught_errors_preserve_termination}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted Prolog source certificate dependency" else ();
\<close>
end
