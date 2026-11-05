theory LP_Prolog_Integer_Recurrence_XML
  imports LP_Prolog_Integer_Recurrence_Check LP_Prolog_Numeric_Row_XML
begin

definition lpp_recurrence_operation_parser where
  "lpp_recurrence_operation_parser =
    (XMLdo (STR ''assignment'') {
      x\<leftarrow>xml_text (STR ''var''); e\<leftarrow>lpp_integer_expression_parser;
      xml_return (LPPRSet x e)}) XMLor
    (XMLdo (STR ''comparison'') {
      f\<leftarrow>xml_text (STR ''predicate''); c\<leftarrow>lpp_numeric_comparison_parser;
      reversed\<leftarrow>xml_bool (STR ''reversed'');
      a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser;
      xml_return (LPPRGuard f c reversed a b)})"

definition lpp_integer_recurrence_parser where
  "lpp_integer_recurrence_parser = XMLdo (STR ''prologIntegerRecurrenceProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    c\<leftarrow>xml_nat (STR ''clause'');
    xs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    ops\<leftarrow>xml_many (STR ''operations'') lpp_recurrence_operation_parser id;
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_integer_expression_parser id;
    coordinates\<leftarrow>xml_many (STR ''coordinates'') (xml_text (STR ''var'')) id;
    loc\<leftarrow>xml_text (STR ''location'');
    child\<leftarrow>xml_singleton (STR ''numericChild'') its4_cpf_parser id;
    xml_return (profile,P,q,modes,c,xs,ops,outputs,coordinates,loc,child)}"

definition check_lpp_integer_recurrence_xml where
  "check_lpp_integer_recurrence_xml xml = (case parse_xml_string lpp_integer_recurrence_parser xml of
    Right (profile,P,q,modes,c,xs,ops,outputs,coordinates,loc,(child,child_answer,prf)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and> \<not>child_answer \<and>
      lpp_check_integer_recurrence P q modes c xs ops outputs coordinates loc child prf
    | _ \<Rightarrow> False)"

theorem check_lpp_integer_recurrence_xml_sound:
  assumes parsed: "parse_xml_string lpp_integer_recurrence_parser xml =
    Right (profile,P,q,modes,c,xs,ops,outputs,coordinates,loc,(child,child_answer,prf))"
    and checked: "check_lpp_integer_recurrence_xml xml"
  shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have source_check: "lpp_check_integer_recurrence P q modes c xs ops outputs coordinates loc child prf"
    using parsed checked by (simp add: check_lpp_integer_recurrence_xml_def)
  show ?thesis by (rule lpp_check_integer_recurrence_sound[OF source_check])
qed

ML \<open>
val checked = [@{thm check_lpp_integer_recurrence_xml_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_its4_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted arithmetic source NO XML dependency" else ();
\<close>
end
