theory LP_Prolog_Finite_Guarded_Composition
 imports LP_Prolog_Finite_Guarded_Region LP_Prolog_Finite_Guarded_Split
   LP_Prolog_Finite_Relational_Return LP_Prolog_Finite_Numeric_Calls
begin

text \<open>These interfaces retain the established finite source regions and
Split contracts while allowing their descent obligations to use a guarded
relation. A numeric child discharges only that relation. Actual successful
helper returns, complete dependency coverage and the source entry remain
separate premises; these lemmas are not a source certificate constructor.\<close>

ML \<open>
val checked = [@{thm lpp_finite_guarded_connection_checked_lower},
  @{thm lpp_finite_guarded_region_contexts_checked_lower},
  @{thm lpp_finite_guarded_split_interface_lower},
  @{thm lpp_finite_relational_return_context},
  @{thm lpp_check_finite_numeric_component_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite guarded composition dependency" else ();
\<close>
end
