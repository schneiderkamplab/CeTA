theory LP_Prolog_Context_Certificate
 imports LP_Prolog_Context_Module_Query LP_Prolog_Context_Module_XML LP_Prolog_Return_Module_XML
begin

theorem lpp_context_module_triples_sound:
  fixes SP :: "string lpp_success_clause list"
    and ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol \<Rightarrow> 'b"
  assumes checked: "lpp_check_context_module_query fuel P Q nds states contexts T typings returned arity acts r q modes"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_triple_calls (set (lp_dependency_triples (lp_roles_program p d Q)))
        (lp_roles_program p d Q))
        {(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpp_context_module_query_sound[where p=p and d=d, OF checked transfer len ground])
  fix us :: "('b,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  show "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule lp_triple_calls_imply_source_termination[OF child[OF length gr]])
qed

definition check_lpp_context_triples where
  "check_lpp_context_triples I J fuel P Q nds states contexts T typings returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs =
    (lpp_check_context_module_query fuel P Q nds states contexts T typings returned arity acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R=lp_roles_program p d Q \<and> D=lp_dependency_triples R \<and>
       q' = p (lpcn_pred (nds!r)) \<and> n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs))"

theorem check_lpp_context_triples_sound:
  fixes SP :: "string lpp_success_clause list"
    and ts :: "(string lp_cut_symbol,string) term list" and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpp_context_triples I J fuel P Q nds states contexts T typings returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpp_context_module_triples_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ transfer len ground])
  show "lpp_check_context_module_query fuel P Q nds states contexts T typings returned arity acts r q modes"
    using ok by (simp add: check_lpp_context_triples_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    using ok by (auto simp: check_lpp_context_triples_def Let_def)
  have "SN_on (lp_triple_calls (set D) R) {(q',map (\<lambda>t. lp_ieval t LPIVar) us)}"
    by (rule check_lp_triple_pidp_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpp_context_triples_def Let_def\<close>)
  then show "SN_on (lp_triple_calls
      (set (lp_dependency_triples (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q)))
      (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
      {(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
    using ok by (auto simp: check_lpp_context_triples_def Let_def)
qed

definition lpp_context_certificate_parser where
  "lpp_context_certificate_parser = XMLdo (STR ''prologContextDependencyTriplesProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    module\<leftarrow>lpp_context_module_parser;
    predicates\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    constructors\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (profile,q,modes,module,predicates,constructors,child)}"

definition check_lpp_context_certificate_xml where
  "check_lpp_context_certificate_xml xml = (case parse_xml_string lpp_context_certificate_parser xml of
    Right (profile,q,modes,(P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,acts,Q),predicates,constructors,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and> lpp_check_transfer_contract summaries SP receipts \<and>
      check_lpp_context_triples tp_rbt_impl dpp_rbt_impl fuel P Q nds states contexts (lpp_transfer_lookup summaries) typings
        returned arity acts r q modes predicates constructors D R outs fallback dnames pnames marks filters q' n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lpp_context_certificate_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_context_certificate_parser xml =
    Right (profile,q,modes,(P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,acts,Q),predicates,constructors,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and checked: "check_lpp_context_certificate_xml xml"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpp_context_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ _ len ground])
    (use parsed checked in \<open>auto simp: check_lpp_context_certificate_xml_def lpp_check_transfer_contract_def\<close>)

ML \<open>
val checked = [@{thm check_lpp_context_certificate_xml_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source certificate dependency" else ();
\<close>
end
