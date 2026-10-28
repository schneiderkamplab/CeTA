theory LP_Prolog_Static_XML
  imports LP_Prolog_Static LP_Cut_SEG_Triple_XML
begin

text \<open>Fixed standalone builtin signature for iso-rational-libraries-v1.
Names use the shared certificate encoding arity:name. The structural source bridge never calls these predicates. No certificate may
supply a smaller builtin environment to make an unsafe call appear ordinary.\<close>
definition lpp_builtin_signature :: "(string \<times> nat) set" where
  "lpp_builtin_signature = set [
    (''0:!'',0),
    (''2:*->'',2),
    (''2:,'',2),
    (''2:->'',2),
    (''2:;'',2),
    (''2:<'',2),
    (''2:='',2),
    (''2:=..'',2),
    (''2:=:='',2),
    (''2:=<'',2),
    (''2:=='',2),
    ((map char_of_nat [50,58,61,92,61]),2),
    (''2:>'',2),
    (''2:>='',2),
    (''2:@<'',2),
    (''2:@=<'',2),
    (''2:@>'',2),
    (''2:@>='',2),
    ((map char_of_nat [49,58,92,43]),1),
    ((map char_of_nat [50,58,92,61]),2),
    ((map char_of_nat [50,58,92,61,61]),2),
    (''1:abolish'',1),
    (''1:acyclic_term'',1),
    (''3:append'',3),
    (''3:arg'',3),
    (''1:assert'',1),
    (''1:asserta'',1),
    (''1:assertz'',1),
    (''0:at_end_of_stream'',0),
    (''1:at_end_of_stream'',1),
    (''1:atom'',1),
    (''2:atom_chars'',2),
    (''2:atom_codes'',2),
    (''3:atom_concat'',3),
    (''2:atom_length'',2),
    (''1:atomic'',1),
    (''3:bagof'',3),
    (''3:between'',3),
    (''1:call'',1),
    (''2:call'',2),
    (''3:call'',3),
    (''4:call'',4),
    (''5:call'',5),
    (''6:call'',6),
    (''7:call'',7),
    (''8:call'',8),
    (''1:callable'',1),
    (''3:catch'',3),
    (''2:char_code'',2),
    (''2:char_conversion'',2),
    (''2:clause'',2),
    (''1:close'',1),
    (''2:close'',2),
    (''3:compare'',3),
    (''1:compound'',1),
    (''1:consult'',1),
    (''2:copy_term'',2),
    (''2:current_char_conversion'',2),
    (''1:current_input'',1),
    (''3:current_op'',3),
    (''1:current_output'',1),
    (''1:current_predicate'',1),
    (''2:current_prolog_flag'',2),
    (''1:cyclic_term'',1),
    (''1:display'',1),
    (''2:display'',2),
    (''1:ensure_loaded'',1),
    (''3:exclude'',3),
    (''0:fail'',0),
    (''0:false'',0),
    (''3:findall'',3),
    (''4:findall'',4),
    (''2:flatten'',2),
    (''1:float'',1),
    (''0:flush_output'',0),
    (''1:flush_output'',1),
    (''4:foldl'',4),
    (''5:foldl'',5),
    (''6:foldl'',6),
    (''7:foldl'',7),
    (''3:functor'',3),
    (''1:get'',1),
    (''1:get0'',1),
    (''1:get_byte'',1),
    (''2:get_byte'',2),
    (''1:get_char'',1),
    (''2:get_char'',2),
    (''1:get_code'',1),
    (''2:get_code'',2),
    (''1:ground'',1),
    (''0:halt'',0),
    (''1:halt'',1),
    (''3:include'',3),
    (''1:initialization'',1),
    (''1:integer'',1),
    (''2:is'',2),
    (''1:is_list'',1),
    (''2:keysort'',2),
    (''2:last'',2),
    (''2:length'',2),
    (''1:listing'',1),
    (''2:maplist'',2),
    (''3:maplist'',3),
    (''4:maplist'',4),
    (''5:maplist'',5),
    (''2:max_list'',2),
    (''2:member'',2),
    (''2:memberchk'',2),
    (''2:min_list'',2),
    (''2:msort'',2),
    (''2:name'',2),
    (''0:nl'',0),
    (''1:nl'',1),
    (''1:nonvar'',1),
    (''1:not'',1),
    (''3:nth0'',3),
    (''4:nth0'',4),
    (''3:nth1'',3),
    (''4:nth1'',4),
    (''1:number'',1),
    (''2:number_chars'',2),
    (''2:number_codes'',2),
    (''3:numbervars'',3),
    (''4:numbervars'',4),
    (''1:once'',1),
    (''3:op'',3),
    (''3:open'',3),
    (''4:open'',4),
    (''3:partition'',3),
    (''1:peek_byte'',1),
    (''2:peek_byte'',2),
    (''1:peek_char'',1),
    (''2:peek_char'',2),
    (''1:peek_code'',1),
    (''2:peek_code'',2),
    (''2:plus'',2),
    (''1:put'',1),
    (''1:put_byte'',1),
    (''2:put_byte'',2),
    (''1:put_char'',1),
    (''2:put_char'',2),
    (''1:put_code'',1),
    (''2:put_code'',2),
    (''1:read'',1),
    (''2:read'',2),
    (''2:read_term'',2),
    (''3:read_term'',3),
    (''0:repeat'',0),
    (''1:retract'',1),
    (''1:retractall'',1),
    (''2:reverse'',2),
    (''1:see'',1),
    (''1:seeing'',1),
    (''0:seen'',0),
    (''3:select'',3),
    (''4:select'',4),
    (''1:set_input'',1),
    (''1:set_output'',1),
    (''2:set_prolog_flag'',2),
    (''3:setof'',3),
    (''2:sort'',2),
    (''4:sort'',4),
    (''2:statistics'',2),
    (''2:stream_property'',2),
    (''5:sub_atom'',5),
    (''4:sub_string'',4),
    (''5:sub_string'',5),
    (''3:sublist'',3),
    (''3:subtract'',3),
    (''2:succ'',2),
    (''3:succ'',3),
    (''2:sum_list'',2),
    (''1:tab'',1),
    (''2:tab'',2),
    (''1:tell'',1),
    (''1:telling'',1),
    (''2:term_variables'',2),
    (''1:throw'',1),
    (''0:told'',0),
    (''0:true'',0),
    (''0:ttynl'',0),
    (''2:unify_with_occurs_check'',2),
    (''1:var'',1),
    (''1:write'',1),
    (''2:write'',2),
    (''1:write_canonical'',1),
    (''2:write_canonical'',2),
    (''2:write_term'',2),
    (''3:write_term'',3),
    (''1:writeq'',1),
    (''2:writeq'',2)]"

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
