theory LP_Prolog_Static_Audit
  imports LP_Prolog_Static_XML
begin
ML \<open>
val audited = [@{thm check_lpp_static_xml_sound},
  @{thm lp_prolog_static_termination}, @{thm lp_prolog_uncaught_errors_preserve_termination}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted Prolog source certificate dependency" else ();
\<close>
end
