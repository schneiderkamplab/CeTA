theory LP_Prolog_Rational_NO_XML
  imports LP_Cut_Rational_NO_Binding LP_Prolog_Static_NO_XML
begin

definition lpcr_goal_parser where
  "lpcr_goal_parser =
    (XMLdo (STR ''atom'') {t\<leftarrow>(xml_nat (STR ''ref'')); xml_return (LPCAtom t)}) XMLor
    (xml_change (xml_nat (STR ''cut'')) (\<lambda>m. xml_return (LPCCut m))) XMLor
    (XMLdo (STR ''true'') {xml_return LPCTrue}) XMLor
    (XMLdo (STR ''fail'') {xml_return LPCFail}) XMLor
    (XMLdo (STR ''meta'') {t\<leftarrow>(xml_nat (STR ''ref'')); xml_return (LPCMeta t)}) XMLor
    (XMLdo (STR ''unify'') {a\<leftarrow>(xml_nat (STR ''ref'')); b\<leftarrow>(xml_nat (STR ''ref'')); xml_return (LPCUnify a b)})"
definition lpcr_entry_parser where
  "lpcr_entry_parser =
    (xml_change (xml_many (STR ''goals'') lpcr_goal_parser id) (\<lambda>gs. xml_return (LPCGoals gs))) XMLor
    (XMLdo (STR ''clauseChoice'') {
      gs\<leftarrow>xml_many (STR ''goals'') lpcr_goal_parser id;
      c\<leftarrow>xml_nat (STR ''index''); m\<leftarrow>xml_nat (STR ''scope''); xml_return (LPCClause gs c m)}) XMLor
    (xml_change (xml_nat (STR ''barrier'')) (\<lambda>m. xml_return (LPCBarrier m)))"

definition lpcr_clash_parser where
  "lpcr_clash_parser =
    (xml_change (xml_many (STR ''constructorClash'') (xml_nat (STR ''index'')) id)
      (\<lambda>p. xml_return (LPRConstructorClash p))) XMLor
    (XMLdo (STR ''repeatedVariableClash'') {
      p\<leftarrow>xml_many (STR ''left'') (xml_nat (STR ''index'')) id;
      q\<leftarrow>xml_many (STR ''right'') (xml_nat (STR ''index'')) id;
      xml_return (LPRRepeatedVariableClash p q)})"

definition lpcr_action_parser where
  "lpcr_action_parser =
    (XMLdo (STR ''admin'') {xml_return LPCRationalAdmin}) XMLor
    (XMLdo (STR ''case'') {m\<leftarrow>xml_nat (STR ''scope''); xml_return (LPCRationalCase m)}) XMLor
    (XMLdo (STR ''resolve'') {
      env\<leftarrow>xml_many (STR ''environment'')
        (xml_pair (STR ''binding'') (xml_text (STR ''var'')) (xml_nat (STR ''ref'')) Pair) id;
      body\<leftarrow>xml_many (STR ''body'') lpcr_goal_parser id;
      xml_return (LPCRationalResolve env body)}) XMLor
    (XMLdo (STR ''backtrack'') {e\<leftarrow>lpcr_clash_parser; xml_return (LPCRationalBacktrack e)})"

definition lpp_rational_no_parser where
  "lpp_rational_no_parser = XMLdo (STR ''prologRationalSourceNonterminationProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    A\<leftarrow>xml_many (STR ''predicates'')
      (xml_pair (STR ''signature'') (xml_text (STR ''name'')) (xml_nat (STR ''arity'')) Pair) id;
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    argv\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
    G\<leftarrow>xml_many (STR ''graph'') (XMLdo (STR ''node'') {
      f\<leftarrow>lpc_symbol_parser;
      js\<leftarrow>xml_many (STR ''children'') (xml_nat (STR ''ref'')) id;
      xml_return (LPRBranch f js :: (string lp_cut_symbol,string) lp_rational_node)}) id;
    anchors\<leftarrow>xml_many (STR ''anchors'') lpc_term_parser id;
    x\<leftarrow>xml_text (STR ''variable'');
    binding_term\<leftarrow>xml_singleton (STR ''rhs'') lpc_term_parser id;
    r\<leftarrow>xml_nat (STR ''bindingRoot'');
    a\<leftarrow>xml_singleton (STR ''call'') lpc_term_parser id;
    i\<leftarrow>xml_nat (STR ''callRoot'');
    before\<leftarrow>xml_many (STR ''before'') lpc_entry_parser id;
    after\<leftarrow>xml_many (STR ''after'') lpcr_entry_parser id;
    initial_steps\<leftarrow>lpc_no_trace_parser (STR ''prefix'');
    steps\<leftarrow>xml_many (STR ''loop'') (XMLdo (STR ''step'') {
      action\<leftarrow>lpcr_action_parser;
      state\<leftarrow>xml_many (STR ''state'') lpcr_entry_parser id;
      xml_return (action,state)}) id;
    xml_return (profile,A,P,q,modes,fuel,argv,G,anchors,x,binding_term,r,a,i,before,after,initial_steps,steps)}"

definition check_lpp_rational_no_xml where
  "check_lpp_rational_no_xml xml = (case parse_xml_string lpp_rational_no_parser xml of
    Right (profile,A,P,q,modes,fuel,argv,G,anchors,x,binding_term,r,a,i,before,after,initial_steps,steps) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and> (q,length modes)\<in>set A \<and>
      list_all (\<lambda>a. a\<notin>lpp_builtin_signature \<and> lpp_defined P a) A \<and>
      lpp_static_program (set A) P \<and>
      lpc_rational_check_source fuel G anchors P q modes argv x binding_term r a i before after initial_steps steps
    | _ \<Rightarrow> False)"

theorem check_lpp_rational_no_xml_sound:
  assumes parsed: "parse_xml_string lpp_rational_no_parser xml =
    Right (profile,A,P,q,modes,fuel,argv,G,anchors,x,binding_term,r,a,i,before,after,initial_steps,steps)"
    and ok: "check_lpp_rational_no_xml xml"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lp_prolog_source P lpp_builtin_signature X)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have child: "lpc_rational_check_source fuel G anchors P q modes argv x binding_term r a i before after initial_steps steps"
    using parsed ok by (simp add: check_lpp_rational_no_xml_def)
  have no: "\<not> SN_on (lp_prolog_source P lpp_builtin_signature X)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
    by (rule lp_prolog_static_nontermination[where A="set A"])
      (use lpc_rational_check_source_sound[OF child] parsed ok in
        \<open>auto simp: check_lpp_rational_no_xml_def lpp_static_state_def list_all_iff lp_cut_state_map_def\<close>)
  show ?thesis using no lpc_rational_check_source_sound[OF child] by blast
qed

ML \<open>
val checked = [@{thm check_lpp_rational_no_xml_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted Prolog rational NO dependency" else ();
\<close>
end
