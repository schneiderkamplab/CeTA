theory LP_Prolog_Undefined_XML
  imports LP_Prolog_Uniform_NO_XML
begin

text \<open>An absent entry predicate raises an uncaught existence error before
any clause body is entered. Definition signatures are complete source context,
not an assumption that every unimplemented operation is an undefined call.\<close>

lemma lp_prolog_source_empty:
  "([],t) \<notin> lp_prolog_source P B X"
  by (auto simp: lp_prolog_source_def lpp_builtin_active_def lpp_undefined_def
      lp_cut_mgu_source_empty)

lemma lp_prolog_undefined_entry:
  assumes missing: "\<not>lpp_defined P (q,length ts)"
    and ordinary: "(q,length ts)\<notin>B"
  shows "SN_on (lp_prolog_source P B X)
    {LPCGoals (LPCAtom (LPIFun (LPCUser q) ts)#gs)#es}"
proof -
  have stopped: "SN_on (lp_prolog_source P B X) {[]}"
    by (rule step_reflects_SN_on) (simp add: lp_prolog_source_empty)
  have undefined: "lpp_undefined P (LPCGoals (LPCAtom (LPIFun (LPCUser q) ts)#gs)#es)"
    using missing by (auto simp: lpp_undefined_def)
  have nb: "\<not> lpp_builtin_active B (LPCGoals (LPCAtom (LPIFun (LPCUser q) ts)#gs)#es)"
    using ordinary by (simp add: lpp_builtin_active_def)
  show ?thesis
    by (rule step_reflects_SN_on)
      (use stopped undefined nb in \<open>auto simp: lp_prolog_source_def\<close>)
qed

definition lpp_undefined_parser where
  "lpp_undefined_parser = XMLdo (STR ''prologUndefinedQueryProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    D\<leftarrow>xml_many (STR ''definitions'')
      (xml_pair (STR ''signature'') (xml_text (STR ''name'')) (xml_nat (STR ''arity'')) Pair) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    xml_return (profile,D,q,modes)}"

definition check_lpp_undefined_xml where
  "check_lpp_undefined_xml xml = (case parse_xml_string lpp_undefined_parser xml of
    Right (profile,D,q,modes) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and>
      (q,length modes)\<notin>lpp_builtin_signature \<and> (q,length modes)\<notin>set D
    | _ \<Rightarrow> False)"

theorem check_lpp_undefined_xml_sound:
  assumes parsed: "parse_xml_string lpp_undefined_parser xml = Right (profile,D,q,modes)"
    and ok: "check_lpp_undefined_xml xml"
    and source: "\<And>a. lpp_defined P a \<longleftrightarrow> a\<in>set D"
    and arity: "length ts=length modes"
  shows "SN_on (lp_prolog_source P lpp_builtin_signature X)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
  by (rule lp_prolog_undefined_entry)
    (use parsed ok source arity in \<open>auto simp: check_lpp_undefined_xml_def\<close>)

end
