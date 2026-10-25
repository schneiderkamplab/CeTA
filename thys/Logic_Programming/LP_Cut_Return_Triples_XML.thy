theory LP_Cut_Return_Triples_XML
  imports LP_Cut_Return_Triples LP_Cut_Return_XML LP_Dependency_Triple_XML
begin

definition check_lpc_return_triples where
  "check_lpc_return_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs =
    (lpc_return_check_root fuel P Q nds states returned arity acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R=lp_roles_program p d Q \<and> D=lp_dependency_triples R \<and>
       q' = p (lpcn_pred (nds!r)) \<and> n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs))"

theorem check_lpc_return_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list" and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpc_return_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpc_return_root_triples_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpc_return_check_root fuel P Q nds states returned arity acts r q modes"
    using ok by (simp add: check_lpc_return_triples_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    using ok by (auto simp: check_lpc_return_triples_def Let_def)
  have "SN_on (lp_triple_calls (set D) R) {(q',map (\<lambda>t. lp_ieval t LPIVar) us)}"
    by (rule check_lp_triple_pidp_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpc_return_triples_def Let_def\<close>)
  then show "SN_on (lp_triple_calls
      (set (lp_dependency_triples (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q)))
      (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
      {(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
    using ok by (auto simp: check_lpc_return_triples_def Let_def)
qed

definition lpc_return_triples_parser where
  "lpc_return_triples_parser = XMLdo (STR ''lpCutReturnDependencyTriplesProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    enc_pred\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    enc_data\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,child)
  }"

definition check_lpc_return_triples_xml where
  "check_lpc_return_triples_xml xml = (case parse_xml_string lpc_return_triples_parser xml of
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      check_lpc_return_triples tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        D R outs fallback dnames pnames marks filters q' n positions labs proofs
    | _\<Rightarrow>False)"

theorem check_lpc_return_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_triples_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpc_return_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_triples_xml_def\<close>)

end
