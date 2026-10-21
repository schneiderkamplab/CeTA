theory LP_TOCL09_Checker
  imports LP_Finite_Checker LP_Infinite_Resolution
begin

theorem check_lp_tocl09_sound:
  fixes ts :: "(('f::{compare_order,countable,showl},nat list) lab,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lp_finite I J P outs fallback names filters q n positions prf"
    and len: "length ts=n"
    and gr: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  interpret tp_spec I by (rule I)
  obtain \<pi> where pi: "afs_of filters = Some \<pi>"
    using ok unfolding check_lp_finite_def by (cases "afs_of filters") auto
  let ?out = "\<lambda>f. case map_of outs f of None \<Rightarrow> f | Some g \<Rightarrow> g"
  let ?u = "lp_u_lookup fallback names"
  interpret lp_translation P id ?out ?u .
  have active: "lp_check_active (fallback # concat names) \<pi> (map fst filters)"
    and query: "lp_check_query \<pi> q n positions"
    and varlist: "list_all (\<lambda>(l,r). vars_term r \<subseteq> vars_term l) (map (af_rule \<pi>) translated)"
    and child: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map (af_rule \<pi>) translated) []) prf)"
    using ok by (auto simp: check_lp_finite_def pi Let_def)
  have vars: "\<And>l r. (l,r) \<in> af_rule \<pi> ` set translated \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  proof -
    fix l r assume mem: "(l,r) \<in> af_rule \<pi> ` set translated"
    have member: "(l,r) \<in> set (map (af_rule \<pi>) translated)" using mem by simp
    show "vars_term r \<subseteq> vars_term l"
      using bspec[OF varlist[unfolded list_all_iff] member] by simp
  qed
  have filter: "lp_filter \<pi> (range (\<lambda>(c,i). ?u c i))"
    by (rule lp_check_active_sound[OF _ active lp_u_range])
      (simp add: afs_of_Some_afs_syms[OF pi])
  have sn: "SN (rstep (af_rule \<pi> ` set translated))"
    using check_trs_termination_proof[OF I J child] by (simp add: SN_qrel_def)
  have ground: "ground (af_term \<pi> (encode (LPCall (q,ts))))"
    using lp_check_query_sound[OF query len gr] by (simp add: lp_tag_def)
  have measured: "lp_iproject \<pi> (iencode (LPICall (q,map (\<lambda>t. lp_ieval t LPIVar) ts)))
      (af_term \<pi> (Fun q ts))"
  proof -
    have empty: "vars_term (af_term \<pi> (Fun q ts)) = {}"
      using ground by (simp add: lp_tag_def ground_vars_term_empty)
    have projection: "lp_iproject \<pi> (lp_ieval (Fun q ts) LPIVar) (af_term \<pi> (Fun q ts) \<cdot> Var)"
      by (rule lp_iproject_ieval_forward) (use empty in blast)
    show ?thesis using projection by (simp add: lp_itag_def)
  qed
  have machine: "SN_on (lp_imachine P) {LPICall (q,map (\<lambda>t. lp_ieval t LPIVar) ts)}"
    by (rule infinite_source_machine_terminates[OF filter sn vars measured])
  show ?thesis using lp_imachine_implies_ld_termination[OF machine] by simp
qed

definition lp_tocl09_parser where
  "lp_tocl09_parser = XMLdo (STR ''lpTocl09TerminationProof'') {
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
    query \<leftarrow> XMLdo (STR ''query'') {
      q \<leftarrow> symbol_parser;
      n \<leftarrow> xml_nat (STR ''arity'');
      positions \<leftarrow> xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
      xml_return (q,n,positions)
    };
    filters \<leftarrow> CPF_Proof_Parser.afs symbol_parser;
    prf \<leftarrow> xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,outs,fallback,names,filters,query,prf)
  }"

definition check_lp_tocl09_xml where
  "check_lp_tocl09_xml xml = (case parse_xml_string lp_tocl09_parser xml of
    Right (P,outs,fallback,names,filters,(q,n,positions),prf) \<Rightarrow>
      check_lp_finite tp_rbt_impl dpp_rbt_impl P outs fallback names filters q n positions prf
    | _ \<Rightarrow> False)"

theorem check_lp_tocl09_xml_sound:
  fixes ts :: "((string,nat list) lab,string) term list"
  assumes "parse_xml_string lp_tocl09_parser xml = Right (P,outs,fallback,names,filters,(q,n,positions),prf)"
    "check_lp_tocl09_xml xml" "length ts=n"
    "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule check_lp_tocl09_sound[OF tp_rbt_impl dpp_rbt_impl _ assms(3,4)])
    (use assms(1,2) in \<open>simp add: check_lp_tocl09_xml_def\<close>)

end
