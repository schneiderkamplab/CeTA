theory LP_Cut_SEG_Projected_Code
  imports LP_Cut_SEG_Projected_Certificate_XML
begin

ML \<open>
val audited = [@{thm check_lpc_seg_projected_certificate_xml_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted projected SEG certificate dependency" else ();
\<close>

export_code open check_lpc_seg_projected_certificate_xml
  in Haskell module_name LP_SEG_Projected_Generated

end
