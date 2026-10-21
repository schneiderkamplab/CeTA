theory LP_Mode_Checker
  imports LP_TOCL09_Checker LP_Mode_Refinement
begin

definition check_lp_modes where
  "check_lp_modes I J P aliases q Q outs fallback names filters q' n positions prf =
    (lp_check_mode_cover P Q aliases \<and> map_of aliases q' = Some q \<and>
     check_lp_finite I J Q outs fallback names filters q' n positions prf)"

theorem check_lp_modes_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_modes I J P aliases q Q outs fallback names filters q' n positions prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?e = "\<lambda>f. case map_of aliases f of None \<Rightarrow> f | Some g \<Rightarrow> g"
  have cover: "lp_mode_cover P Q ?e (map fst aliases)"
    by (rule lp_check_mode_cover_sound) (use ok in \<open>simp add: check_lp_modes_def\<close>)
  have mapping: "map_of aliases q' = Some q" using ok by (simp add: check_lp_modes_def)
  have member: "q' \<in> set (map fst aliases)"
    using mapping by (metis domI dom_map_of_conv_image_fst list.set_map)
  have child: "check_lp_finite I J Q outs fallback names filters q' n positions prf"
    using ok by (simp add: check_lp_modes_def)
  have sn: "SN_on (lp_ild Q) {[(q',map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule check_lp_tocl09_sound[OF I J child len gr])
  have source: "SN_on (lp_ild P)
      {map (lp_mode_atom ?e) [(q',map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
    by (rule lp_mode_termination[OF cover sn]) (use member in simp)
  show ?thesis using source by (simp add: lp_mode_atom_def mapping)
qed

definition lp_mode_tocl09_parser where
  "lp_mode_tocl09_parser = XMLdo (STR ''lpTocl09ModeTerminationProof'') {
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
    child \<leftarrow> lp_tocl09_parser;
    xml_return (P,query,aliases,child)
  }"

definition check_lp_mode_tocl09_xml where
  "check_lp_mode_tocl09_xml xml = (case parse_xml_string lp_mode_tocl09_parser xml of
    Right (P,(q,n,g0),aliases,(Q,outs,fallback,names,filters,(q',n_child,g1),prf)) \<Rightarrow>
      n=n_child \<and> g0=g1 \<and>
      check_lp_modes tp_rbt_impl dpp_rbt_impl P aliases q Q outs fallback names filters q' n g0 prf
    | _ \<Rightarrow> False)"

theorem check_lp_mode_tocl09_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_mode_tocl09_parser xml =
      Right (P,(q,n,positions),aliases,(Q,outs,fallback,names,filters,(q',n_child,g1),prf))"
    and ok: "check_lp_mode_tocl09_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  have accepted: "check_lp_modes tp_rbt_impl dpp_rbt_impl P aliases q Q outs fallback names filters q' n positions prf"
    using parsed ok by (auto simp: check_lp_mode_tocl09_xml_def)
  show ?thesis by (rule check_lp_modes_sound[OF tp_rbt_impl dpp_rbt_impl accepted len gr])
qed

definition check_lp_tocl09_any_xml where
  "check_lp_tocl09_any_xml xml = (check_lp_tocl09_xml xml \<or> check_lp_mode_tocl09_xml xml)"

end
