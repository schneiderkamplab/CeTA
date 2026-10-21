theory LP_PiDP_XML
  imports LP_PiDP_Checker
begin

definition lp_pidp_parser where
  "lp_pidp_parser = XMLdo (STR ''lpTocl09PiDpTerminationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    outs \<leftarrow> xml_many (STR ''returns'')
      (xml_pair (STR ''return'') symbol_parser symbol_parser Pair) id;
    fallback \<leftarrow> xml_singleton (STR ''fallback'') symbol_parser id;
    names \<leftarrow> xml_many (STR ''continuations'')
      (xml_many (STR ''clause'') symbol_parser id) id;
    marks \<leftarrow> xml_many (STR ''marks'')
      (xml_pair (STR ''mark'') symbol_parser symbol_parser Pair) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    filters \<leftarrow> CPF_Proof_Parser.afs symbol_parser;
    labs \<leftarrow> xml_many (STR ''ranks'') (xml_nat (STR ''rank'')) id;
    proofs \<leftarrow> xml_many (STR ''components'')
      (xml_leaf (STR ''noCycle'') None XMLor
        xml_singleton (STR ''component'')
          (xml2dp_termination_proof symbol_parser Mapping.empty Mapping.empty) Some) id;
    xml_return (P,outs,fallback,names,marks,filters,query,labs,proofs)
  }"

definition check_lp_pidp_xml where
  "check_lp_pidp_xml xml = (case parse_xml_string lp_pidp_parser xml of
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),labs,proofs) \<Rightarrow>
      check_lp_pidp tp_rbt_impl dpp_rbt_impl P outs fallback names marks filters q n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lp_pidp_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_pidp_parser xml =
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),labs,proofs)"
    and ok: "check_lp_pidp_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule check_lp_pidp_sound[OF tp_rbt_impl dpp_rbt_impl _ len gr])
    (use parsed ok in \<open>simp add: check_lp_pidp_xml_def\<close>)

definition lp_pidp_mode_parser where
  "lp_pidp_mode_parser = XMLdo (STR ''lpTocl09PiDpModeTerminationProof'') {
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
    aliases \<leftarrow> xml_many (STR ''modes'')
      (xml_pair (STR ''mode'') symbol_parser symbol_parser Pair) id;
    child \<leftarrow> lp_pidp_parser;
    xml_return (P,query,aliases,child)
  }"

definition check_lp_pidp_mode_xml where
  "check_lp_pidp_mode_xml xml = (case parse_xml_string lp_pidp_mode_parser xml of
    Right (P,(q,n,g0),aliases,(Q,outs,fallback,names,marks,filters,(q',n_child,g1),labs,proofs)) \<Rightarrow>
      n=n_child \<and> g0=g1 \<and> lp_check_mode_cover P Q aliases \<and> map_of aliases q'=Some q \<and>
      check_lp_pidp tp_rbt_impl dpp_rbt_impl Q outs fallback names marks filters q' n g0 labs proofs
    | _ \<Rightarrow> False)"

theorem check_lp_pidp_mode_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_pidp_mode_parser xml =
    Right (P,(q,n,positions),aliases,(Q,outs,fallback,names,marks,filters,(q',n_child,g1),labs,proofs))"
    and ok: "check_lp_pidp_mode_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?e = "\<lambda>f. case map_of aliases f of None \<Rightarrow> f | Some g \<Rightarrow> g"
  have cover: "lp_mode_cover P Q ?e (map fst aliases)"
    by (rule lp_check_mode_cover_sound)
       (use parsed ok in \<open>simp add: check_lp_pidp_mode_xml_def\<close>)
  have mapping: "map_of aliases q'=Some q"
    using parsed ok by (auto simp: check_lp_pidp_mode_xml_def)
  have member: "q'\<in>set (map fst aliases)"
    using mapping by (metis domI dom_map_of_conv_image_fst list.set_map)
  have child: "check_lp_pidp tp_rbt_impl dpp_rbt_impl Q outs fallback names marks filters q' n positions labs proofs"
    using parsed ok by (auto simp: check_lp_pidp_mode_xml_def)
  have sn: "SN_on (lp_ild Q) {[(q',map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule check_lp_pidp_sound[OF tp_rbt_impl dpp_rbt_impl child len gr])
  have source: "SN_on (lp_ild P) {map (lp_mode_atom ?e) [(q',map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule lp_mode_termination[OF cover sn]) (use member in simp)
  show ?thesis using source by (simp add: lp_mode_atom_def mapping)
qed

definition check_lp_tocl09_pidp_any_xml where
  "check_lp_tocl09_pidp_any_xml xml = (check_lp_tocl09_any_xml xml \<or> check_lp_pidp_xml xml \<or> check_lp_pidp_mode_xml xml)"

end
