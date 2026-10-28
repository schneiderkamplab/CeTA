theory LP_Prolog_Static_NO_XML
  imports LP_Prolog_Static_NO LP_Prolog_Static_XML LP_Cut_NO_XML
begin

definition lpp_static_no_parser where
  "lpp_static_no_parser = XMLdo (STR ''prologStaticNonterminationProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    A\<leftarrow>xml_many (STR ''predicates'')
      (xml_pair (STR ''signature'') (xml_text (STR ''name'')) (xml_nat (STR ''arity'')) Pair) id;
    child\<leftarrow>lpc_no_certificate_parser;
    xml_return (profile,A,child)}"

definition check_lpp_static_no_xml where
  "check_lpp_static_no_xml xml = (case parse_xml_string lpp_static_no_parser xml of
    Right (profile,A,(P,q,modes,fuel,argv,a,before,after,initial_steps,steps)) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and> (q,length modes)\<in>set A \<and>
      list_all (\<lambda>a. a\<notin>lpp_builtin_signature \<and> lpp_defined P a) A \<and>
      lpp_static_program (set A) P \<and>
      lpc_no_check_source fuel P q modes argv a before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpp_static_no_xml_sound:
  assumes parsed: "parse_xml_string lpp_static_no_parser xml =
    Right (profile,A,(P,q,modes,fuel,argv,a,before,after,initial_steps,steps))"
    and ok: "check_lpp_static_no_xml xml"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_prolog_source P lpp_builtin_signature X)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have child: "lpc_no_check_source fuel P q modes argv a before after initial_steps steps"
    using parsed ok by (simp add: check_lpp_static_no_xml_def)
  have no: "\<not> SN_on (lp_prolog_source P lpp_builtin_signature X)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
    by (rule lp_prolog_static_nontermination[where A="set A"])
      (use lpc_no_check_source_sound[OF child] parsed ok in
        \<open>auto simp: check_lpp_static_no_xml_def lpp_static_state_def list_all_iff\<close>)
  show ?thesis using no lpc_no_check_source_sound[OF child] by blast
qed

end
