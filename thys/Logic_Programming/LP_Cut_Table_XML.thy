theory LP_Cut_Table_XML
  imports LP_Cut_Table_Certificate
begin

derive compare_order lp_cut_symbol

fun lpc_scope_absent where
  "lpc_scope_absent m (LPCGoals gs) = list_all (\<lambda>g. m \<notin> lp_cut_goal_scopes g) gs"
| "lpc_scope_absent m (LPCClause gs c n) = (m \<noteq> n \<and> list_all (\<lambda>g. m \<notin> lp_cut_goal_scopes g) gs)"
| "lpc_scope_absent m (LPCBarrier n) = (m \<noteq> n)"

lemma lpc_scope_absent_correct:
  "lpc_scope_absent m e = (m \<notin> lp_cut_entry_scopes e)"
  by (cases e) (auto simp: list_all_iff)

lemma lp_cut_fresh_code[code]:
  "lp_cut_fresh m es = list_all (lpc_scope_absent m) es"
  by (auto simp: lp_cut_fresh_def list_all_iff lpc_scope_absent_correct)

lemma lp_cut_slice_code[code]:
  "lp_cut_slice P f n = filter (\<lambda>c. case fst (P!c) of
    Fun g ts \<Rightarrow> g=f \<and> length ts=n | Var x \<Rightarrow> False) [0..<length P]"
  unfolding lp_cut_slice_def by (intro filter_cong refl) (auto split: term.splits)

instantiation lp_cut_symbol :: (showl) showl
begin
fun showsl_lp_cut_symbol where
  "showsl_lp_cut_symbol (LPCUser f) = showsl f"
| "showsl_lp_cut_symbol LPCBang = showsl_lit (STR ''!'')"
| "showsl_lp_cut_symbol LPCComma = showsl_lit (STR '','')"
| "showsl_lp_cut_symbol LPCEquals = showsl_lit (STR ''='')"
| "showsl_lp_cut_symbol LPCTruth = showsl_lit (STR ''true'')"
| "showsl_lp_cut_symbol LPCFailure = showsl_lit (STR ''fail'')"
| "showsl_lp_cut_symbol LPCCallSymbol = showsl_lit (STR ''call'')"
definition "showsl_list (xs::'a lp_cut_symbol list) = default_showsl_list showsl xs"
instance ..
end

definition lpc_symbol_parser where
  "lpc_symbol_parser = xml_change (xml_text (STR ''user'')) (\<lambda>s. xml_return (LPCUser s)) XMLor
    (XMLdo (STR ''bangSymbol'') {xml_return LPCBang}) XMLor
    (XMLdo (STR ''commaSymbol'') {xml_return LPCComma}) XMLor
    (XMLdo (STR ''equalsSymbol'') {xml_return LPCEquals}) XMLor
    (XMLdo (STR ''trueSymbol'') {xml_return LPCTruth}) XMLor
    (XMLdo (STR ''failSymbol'') {xml_return LPCFailure}) XMLor
    (XMLdo (STR ''callSymbol'') {xml_return LPCCallSymbol})"
definition lpc_term_parser where
  "lpc_term_parser = CPF_Input_Parser.term lpc_symbol_parser Mapping.empty"
definition lpc_goal_parser where
  "lpc_goal_parser =
    (XMLdo (STR ''atom'') {t\<leftarrow>lpc_term_parser; xml_return (LPCAtom t)}) XMLor
    (xml_change (xml_nat (STR ''cut'')) (\<lambda>m. xml_return (LPCCut m))) XMLor
    (XMLdo (STR ''true'') {xml_return LPCTrue}) XMLor
    (XMLdo (STR ''fail'') {xml_return LPCFail}) XMLor
    (XMLdo (STR ''meta'') {t\<leftarrow>lpc_term_parser; xml_return (LPCMeta t)}) XMLor
    (XMLdo (STR ''unify'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser; xml_return (LPCUnify a b)})"
definition lpc_entry_parser where
  "lpc_entry_parser =
    (xml_change (xml_many (STR ''goals'') lpc_goal_parser id) (\<lambda>gs. xml_return (LPCGoals gs))) XMLor
    (XMLdo (STR ''clauseChoice'') {
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      c\<leftarrow>xml_nat (STR ''index''); m\<leftarrow>xml_nat (STR ''scope''); xml_return (LPCClause gs c m)}) XMLor
    (xml_change (xml_nat (STR ''barrier'')) (\<lambda>m. xml_return (LPCBarrier m)))"
definition lpc_guard_parser where
  "lpc_guard_parser =
    (XMLdo (STR ''headGuard'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      v\<leftarrow>xml_bool (STR ''unifies''); xml_return (LPCHeadGuard a b v)}) XMLor
    (XMLdo (STR ''equalityGuard'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      v\<leftarrow>xml_bool (STR ''unifies''); xml_return (LPCEqGuard a b v)})"
definition lpc_bindings_parser where
  "lpc_bindings_parser = xml_many (STR ''bindings'')
    (xml_pair (STR ''binding'') (xml_text (STR ''var'')) lpc_term_parser Pair) id"
definition lpc_link_parser where
  "lpc_link_parser = XMLdo (STR ''link'') {
    j\<leftarrow>xml_nat (STR ''target'');
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    ts\<leftarrow>xml_many (STR ''terms'') lpc_term_parser id;
    s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
    G\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    K\<leftarrow>xml_many (STR ''guards'') lpc_guard_parser id;
    bindings\<leftarrow>lpc_bindings_parser;
    swaps\<leftarrow>xml_many (STR ''swaps'') (xml_pair (STR ''swap'') (xml_nat (STR ''scope'')) (xml_nat (STR ''scope'')) Pair) id;
    ls\<leftarrow>xml_many (STR ''lhs'') lpc_term_parser id;
    rs\<leftarrow>xml_many (STR ''rhs'') lpc_term_parser id;
    xml_return \<lparr>lpcl_target=j,lpcl_vars=vs,lpcl_terms=ts,lpcl_state=s,lpcl_ground=G,lpcl_guards=K,
      lpcl_bindings=bindings,lpcl_swaps=swaps,lpcl_lhs=ls,lpcl_rhs=rs\<rparr>
  }"
definition lpc_node_parser where
  "lpc_node_parser = XMLdo (STR ''node'') {
    s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
    G\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    K\<leftarrow>xml_many (STR ''guards'') lpc_guard_parser id;
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
    xml_return \<lparr>lpcn_state=s,lpcn_ground=G,lpcn_guards=K,lpcn_vars=vs,lpcn_pred=f\<rparr>
  }"
definition lpc_mode_parser where
  "lpc_mode_parser =
    (XMLdo (STR ''alwaysSuccess'') {xml_return LPCAlwaysSuccess}) XMLor
    (XMLdo (STR ''alwaysFailure'') {xml_return LPCAlwaysFailure}) XMLor
    (XMLdo (STR ''both'') {xml_return LPCBoth})"
definition lpc_action_parser where
  "lpc_action_parser =
    (XMLdo (STR ''terminal'') {xml_return LPCATerminal}) XMLor
    (XMLdo (STR ''inconsistent'') {xml_return LPCAInconsistent}) XMLor
    (XMLdo (STR ''refutedGuard'') {
      i\<leftarrow>xml_nat (STR ''index''); k\<leftarrow>xml_nat (STR ''prefix'');
      bindings\<leftarrow>lpc_bindings_parser; xml_return (LPCARefutedGuard i k bindings)}) XMLor
    (XMLdo (STR ''controlResidual'') {
      Fs\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      roles\<leftarrow>xml_many (STR ''roles'') (xml_pair (STR ''encoding'') lpc_symbol_parser lpc_symbol_parser Pair) id;
      xml_return (LPCAControl Fs roles)}) XMLor
    (XMLdo (STR ''plain'') {
      Fs\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      roles\<leftarrow>xml_many (STR ''roles'') (xml_pair (STR ''encoding'') lpc_symbol_parser lpc_symbol_parser Pair) id;
      xml_return (LPCAPlain Fs roles)}) XMLor
    (xml_change (xml_many (STR ''stackSplit'') lpc_link_parser id)
      (\<lambda>es. xml_return (LPCAStack es))) XMLor
    (XMLdo (STR ''admin'') {s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      e\<leftarrow>lpc_link_parser; xml_return (LPCAAdmin s e)}) XMLor
    (XMLdo (STR ''trim'') {s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      bs\<leftarrow>xml_many (STR ''suffix'') lpc_entry_parser id;
      e\<leftarrow>lpc_link_parser; xml_return (LPCATrim s bs e)}) XMLor
    (XMLdo (STR ''allocate'') {f\<leftarrow>xml_text (STR ''predicate'');
      ts\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      es\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id;
      m\<leftarrow>xml_nat (STR ''scope''); s\<leftarrow>xml_many (STR ''state'') lpc_entry_parser id;
      e\<leftarrow>lpc_link_parser; xml_return (LPCACase f ts gs es m s e)}) XMLor
    (XMLdo (STR ''metaCall'') {a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      es\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id; m\<leftarrow>xml_nat (STR ''scope'');
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id;
      e\<leftarrow>lpc_link_parser; xml_return (LPCAMeta a gs es m bs e)}) XMLor
    (XMLdo (STR ''resolve'') {a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      c\<leftarrow>xml_nat (STR ''index''); m\<leftarrow>xml_nat (STR ''scope'');
      es\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id;
      k\<leftarrow>xml_nat (STR ''activePrefix''); l\<leftarrow>xml_nat (STR ''clausePrefix'');
      A\<leftarrow>xml_many (STR ''anchors'') (xml_text (STR ''var'')) id;
      s\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      ts\<leftarrow>xml_many (STR ''anchorTerms'') lpc_term_parser id;
      bindings\<leftarrow>lpc_bindings_parser; mode\<leftarrow>lpc_mode_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPCAResolution a gs c m es k l A s ts bindings mode yes no)}) XMLor
    (XMLdo (STR ''equality'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      es\<leftarrow>xml_many (STR ''saved'') lpc_entry_parser id;
      k\<leftarrow>xml_nat (STR ''activePrefix''); l\<leftarrow>xml_nat (STR ''clausePrefix'');
      s\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id; mode\<leftarrow>lpc_mode_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPCAEquality a b gs es k l s mode yes no)})"
definition lpc_atom_parser where
  "lpc_atom_parser = xml_change lpc_term_parser (\<lambda>t. case t of Fun f ts\<Rightarrow>xml_return (f,ts)
    | _\<Rightarrow>xml_error (STR ''cut residual atom expected''))"
definition lpc_certificate_parser where
  "lpc_certificate_parser = XMLdo (STR ''lpCutGraphTerminationProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate''); modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    acts\<leftarrow>xml_many (STR ''actions'') lpc_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    enc_pred\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    enc_data\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_tocl09_parser;
    xml_return (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,child)
  }"
definition check_lpc_xml where
  "check_lpc_xml xml = (case parse_xml_string lpc_certificate_parser xml of
    Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,filters,(q',n,positions),prf))\<Rightarrow>
      check_lpc_tocl tp_rbt_impl dpp_rbt_impl fuel P Q nds acts r q modes enc_pred enc_data
        R outs fallback names filters q' n positions prf
    | _\<Rightarrow>False)"

theorem check_lpc_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_certificate_parser xml =
    Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,filters,(q',n,positions),prf))"
    and ok: "check_lpc_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_tocl_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_xml_def\<close>)

text \<open>Diagnostics do not participate in acceptance. The initial bits are
parse, bounds, source, root, residual encoding, query encoding, query modes,
child proof; the remainder reports the local action checks.\<close>
definition lpc_xml_diagnostics where
  "lpc_xml_diagnostics xml = (case parse_xml_string lpc_certificate_parser xml of
    Right (P,q,modes,fuel,r,nds,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,filters,(q',n,positions),prf))\<Rightarrow>
      (if r\<ge>length nds \<or> length nds\<noteq>length acts then [True,False] else
       let p=lpc_lookup fallback enc_pred; d=lpc_lookup fallback enc_data; nd=nds!r in
       [True,True,lp_cut_source_program P,
        lp_cut_check_root q modes (lpcn_vars nd) (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd),
        R=lp_roles_program p d Q, q' = p (lpcn_pred nd), n=length modes \<and> positions=lpc_positions modes,
        check_lp_finite tp_rbt_impl dpp_rbt_impl R outs fallback names filters q' n positions prf] @
       map (\<lambda>i. lpc_check_action fuel P Q nds (nds!i) (acts!i)) [0..<length nds])
    | _\<Rightarrow>[False])"

end
