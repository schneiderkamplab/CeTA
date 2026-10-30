theory LP_Prolog_Static_XML
  imports LP_Prolog_Builtin_Signature LP_Cut_SEG_Triple_XML
begin

declare lpp_static_template.simps[code del]
lemma lpp_static_template_code[code]:
  "lpp_static_template A g = (case g of
    LPCAtom (Fun (LPCUser f) ts) \<Rightarrow> (f,length ts)\<in>A
  | LPCAtom _ \<Rightarrow> False | LPCMeta _ \<Rightarrow> False
  | LPCExpand _ _ \<Rightarrow> False | _ \<Rightarrow> True)"
  by (cases g) (auto split: term.splits lp_cut_symbol.splits)

definition lpp_static_parser where
  "lpp_static_parser = XMLdo (STR ''prologStaticSEGProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    A\<leftarrow>xml_many (STR ''predicates'')
      (xml_pair (STR ''signature'') (xml_text (STR ''name'')) (xml_nat (STR ''arity'')) Pair) id;
    child\<leftarrow>lpc_seg_triples_parser;
    xml_return (profile,A,child)}"

definition check_lpp_static_xml where
  "check_lpp_static_xml xml = (case parse_xml_string lpp_static_parser xml of
    Right (profile,A,(P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))) \<Rightarrow>
      profile = ''iso-rational-libraries-v1'' \<and> (q,length modes)\<in>set A \<and>
      list_all (\<lambda>a. a\<notin>lpp_builtin_signature) A \<and>
      lpp_static_program (set A) P \<and>
      check_lpc_seg_triples tp_rbt_impl dpp_rbt_impl fuel P D Q roots blocks q modes chain_pred enc_pred enc_data
        D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lpp_static_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_static_parser xml =
    Right (profile,A,(P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)))"
    and ok: "check_lpp_static_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_prolog_extension P lpp_builtin_signature X E)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lp_prolog_static_termination[where A="set A"])
  show "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
    by (rule check_lpc_seg_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
      (use parsed ok in \<open>auto simp: check_lpp_static_xml_def\<close>)
qed (use parsed ok len in \<open>auto simp: check_lpp_static_xml_def lpp_static_state_def list_all_iff\<close>)

end
