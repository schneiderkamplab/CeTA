theory LP_Source_Simplify_XML
  imports LP_Source_Simplify LP_PiDP_XML
begin

definition lp_simplify_parser where
  "lp_simplify_parser = XMLdo (STR ''lpTocl09SimplificationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    child \<leftarrow> lp_pidp_mode_parser;
    xml_return (P,query,child)
  }"

definition check_lp_simplify_xml where
  "check_lp_simplify_xml xml = (case parse_xml_string lp_simplify_parser xml of
    Right (P,(q,n,g0),(Q,(q1,n1,g1),aliases,
      (T,outs,fallback,names,marks,filters,(q2,n2,g2),labs,proofs))) \<Rightarrow>
      Q=lp_live_clauses P \<and> q=q1 \<and> n=n1 \<and> n=n2 \<and> g0=g1 \<and> g0=g2 \<and>
      lp_check_mode_cover Q T aliases \<and> map_of aliases q2=Some q \<and>
      check_lp_pidp tp_rbt_impl dpp_rbt_impl T outs fallback names marks filters q2 n g0 labs proofs
    | _ \<Rightarrow> False)"

theorem check_lp_simplify_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_simplify_parser xml =
    Right (P,(q,n,positions),(Q,(q1,n1,g1),aliases,
      (T,outs,fallback,names,marks,filters,(q2,n2,g2),labs,proofs)))"
    and ok: "check_lp_simplify_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?e = "\<lambda>f. case map_of aliases f of None \<Rightarrow> f | Some g \<Rightarrow> g"
  have cover: "lp_mode_cover Q T ?e (map fst aliases)"
    by (rule lp_check_mode_cover_sound)
      (use parsed ok in \<open>auto simp: check_lp_simplify_xml_def\<close>)
  have mapping: "map_of aliases q2=Some q"
    and reduced: "Q=lp_live_clauses P"
    and child: "check_lp_pidp tp_rbt_impl dpp_rbt_impl T outs fallback names marks filters q2 n positions labs proofs"
    using parsed ok by (auto simp: check_lp_simplify_xml_def)
  have member: "q2\<in>set (map fst aliases)"
    using mapping by (metis domI dom_map_of_conv_image_fst list.set_map)
  have sn: "SN_on (lp_ild T) {[(q2,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule check_lp_pidp_sound[OF tp_rbt_impl dpp_rbt_impl child len gr])
  have source: "SN_on (lp_ild Q) {map (lp_mode_atom ?e) [(q2,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule lp_mode_termination[OF cover sn]) (use member in simp)
  have live: "SN_on (lp_ild (lp_live_clauses P)) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    using source by (simp add: reduced lp_mode_atom_def mapping)
  show ?thesis by (rule lp_live_clauses_sound[OF live])
qed

definition check_lp_full_xml where
  "check_lp_full_xml xml = (check_lp_tocl09_pidp_any_xml xml \<or> check_lp_simplify_xml xml)"

end
