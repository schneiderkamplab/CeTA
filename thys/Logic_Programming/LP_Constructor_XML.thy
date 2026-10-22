theory LP_Constructor_XML
  imports LP_Constructor_Checker LP_SEG_Residual_XML
begin

definition lp_constructor_parser where
  "lp_constructor_parser = XMLdo (STR ''lpConstructorQDpTerminationProof'') {
    P \<leftarrow> xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h \<leftarrow> xml_singleton (STR ''head'') lp_atom_parser id;
      bs \<leftarrow> xml_many (STR ''body'') lp_atom_parser id;
      xml_return (h,bs)
    }) id;
    outs \<leftarrow> xml_many (STR ''returns'')
      (xml_pair (STR ''return'') symbol_parser symbol_parser Pair) id;
    fallback \<leftarrow> xml_singleton (STR ''fallback'') symbol_parser id;
    names \<leftarrow> xml_many (STR ''continuations'')
      (xml_many (STR ''clause'') symbol_parser id) id;
    marks \<leftarrow> xml_many (STR ''marks'')
      (xml_pair (STR ''mark'') symbol_parser symbol_parser Pair) id;
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    filters \<leftarrow> CPF_Proof_Parser.afs symbol_parser;
    seed \<leftarrow> xml_singleton (STR ''seed'') symbol_parser id;
    nfs \<leftarrow>[False] xml_bool (STR ''normalSubstitutions'');
    prf \<leftarrow> xml2dp_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,outs,fallback,names,marks,filters,query,seed,nfs,prf)
  }"

definition check_lp_constructor_xml where
  "check_lp_constructor_xml xml = (case parse_xml_string lp_constructor_parser xml of
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),seed,nfs,prf) \<Rightarrow>
      check_lp_constructor tp_rbt_impl dpp_rbt_impl P outs fallback names marks filters q n positions seed nfs prf
    | _ \<Rightarrow> False)"

theorem check_lp_constructor_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_constructor_parser xml =
    Right (P,outs,fallback,names,marks,filters,(q,n,positions),seed,nfs,prf)"
    and ok: "check_lp_constructor_xml xml" and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule check_lp_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len gr])
    (use parsed ok in \<open>simp add: check_lp_constructor_xml_def\<close>)

definition lp_residual_constructor_parser where
  "lp_residual_constructor_parser = XMLdo (STR ''lpAnswerGraphTerminationProof'') {
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
    fuel \<leftarrow> xml_nat (STR ''fuel'');
    root_id \<leftarrow> xml_nat (STR ''root'');
    nds \<leftarrow> xml_many (STR ''nodes'') (XMLdo (STR ''node'') {
      gs \<leftarrow> xml_many (STR ''goals'') lp_atom_parser id;
      vs \<leftarrow> xml_many (STR ''variables'') lp_seg_variable_parser id;
      f \<leftarrow> xml_singleton (STR ''symbol'') symbol_parser id;
      act \<leftarrow> lp_seg_action_parser;
      xml_return (gs,vs,f,act)
    }) id;
    child \<leftarrow> lp_constructor_parser;
    xml_return (P,query,fuel,root_id,nds,child)
  }"

definition check_lp_residual_constructor where
  "check_lp_residual_constructor I J fuel P nds root_id q n positions Q outs fallback names marks filters q' seed nfs prf =
    (lp_check_residual_graph fuel P Q nds root_id \<and>
     lp_residual_goals nds root_id=[(q,map Var (lp_source_query_args n))] \<and>
     lp_residual_vars nds root_id=lp_source_query_args n \<and>
     lp_residual_symbol nds root_id=q' \<and>
     check_lp_constructor I J Q outs fallback names marks filters q' n positions seed nfs prf)"

theorem check_lp_residual_constructor_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_residual_constructor I J fuel P nds root_id q n positions Q outs fallback names marks filters q' seed nfs prf"
    and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?rho = "\<lambda>x. ?vals!(length x-1)"
  have child: "check_lp_constructor I J Q outs fallback names marks filters q' n positions seed nfs prf"
    using ok by (simp add: check_lp_residual_constructor_def)
  have sn: "SN_on (lp_ild Q) {[(q',?vals)]}"
    by (rule check_lp_constructor_sound[OF I J child len ground])
  have eval: "map ?rho (lp_source_query_args n)=?vals"
    using lp_source_query_eval[of ?vals] len by simp
  have source: "SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a ?rho) (lp_residual_goals nds root_id)}"
    by (rule lp_check_residual_graph_sound)
      (use ok sn eval in \<open>auto simp: check_lp_residual_constructor_def\<close>)
  show ?thesis using source ok eval
    by (simp add: check_lp_residual_constructor_def lp_atom_eval_def o_def)
qed

definition check_lp_residual_constructor_xml where
  "check_lp_residual_constructor_xml xml = (case parse_xml_string lp_residual_constructor_parser xml of
    Right (P,(q,n,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,marks,filters,(q',n',positions'),seed,nfs,prf)) \<Rightarrow>
      n' = n \<and> positions' = positions \<and>
      check_lp_residual_constructor tp_rbt_impl dpp_rbt_impl fuel P nds root_id q n positions
        Q outs fallback names marks filters q' seed nfs prf
    | _ \<Rightarrow> False)"

theorem check_lp_residual_constructor_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes parsed: "parse_xml_string lp_residual_constructor_parser xml =
    Right (P,(q,n,positions),fuel,root_id,nds,
      (Q,outs,fallback,names,marks,filters,(q',n',positions'),seed,nfs,prf))"
    and checked: "check_lp_residual_constructor_xml xml" and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  have valid: "check_lp_residual_constructor tp_rbt_impl dpp_rbt_impl fuel P nds root_id q n positions
    Q outs fallback names marks filters q' seed nfs prf"
    using parsed checked by (simp add: check_lp_residual_constructor_xml_def)
  show ?thesis by (rule check_lp_residual_constructor_sound[OF tp_rbt_impl dpp_rbt_impl valid len ground])
qed

definition check_lp_constructor_any_xml where
  "check_lp_constructor_any_xml xml = (check_lp_answer_full_xml xml \<or> check_lp_constructor_xml xml \<or> check_lp_residual_constructor_xml xml)"

end
