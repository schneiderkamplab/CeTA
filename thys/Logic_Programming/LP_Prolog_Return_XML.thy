theory LP_Prolog_Return_XML
  imports LP_Prolog_Return_Check LP_Cut_Return_Triples_XML
begin

definition lpp_return_check_root where
  "lpp_return_check_root fuel P Q nds states returned arity acts r q modes =
    (lp_cut_source_program P \<and> r<length nds \<and>
     lpp_check_return_table fuel P Q nds states returned arity acts \<and>
     lp_cut_check_root q modes (lpcn_vars (nds!r)) (lpcn_state (nds!r))
       (lpcn_ground (nds!r)) (lpcn_guards (nds!r)))"

theorem lpp_return_root_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol\<Rightarrow>'b"
  assumes checked: "lpp_return_check_root fuel P Q nds states returned arity acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_ild (lp_roles_program p d Q))
        {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
  shows "SN_on (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "nds!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and table: "lpp_check_return_table fuel P Q nds states returned arity acts" and bound: "r<length nds"
    and program: "lp_cut_source_program P"
    using checked by (auto simp: lpp_return_check_root_def)
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have mapped: "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred ?nd),map (\<lambda>t. lp_ieval t LPIVar) (map (map_term d id) ts))]}"
    by (rule child) (use len ground in \<open>auto simp: lpc_positions_def\<close>)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lp_roles_termination_reflect[where p=p and d=d])
      (use mapped vals in \<open>simp add: lp_roles_iatom_def map_map o_def lp_map_finite_eval\<close>)
  have contract: "lpp_return_contract P lpp_builtin_signature lpp_test_builtin (lpc_return_eval ?env (states!r)) (lp_ild Q)
    [(lpcn_pred ?nd,map ?env ?vs)] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_check_return_table_contract[OF table program bound known residual])
  have state: "map fst (states!r)=lpcn_state ?nd"
    using table bound by (auto simp: lpp_check_return_table_def list_all_iff)
  have source: "SN_on (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    using contract by (simp add: lpp_return_contract_def lpc_return_eval_erases state)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

theorem lpp_return_root_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
    and p d :: "string lp_cut_symbol \<Rightarrow> 'b"
  assumes checked: "lpp_return_check_root fuel P Q nds states returned arity acts r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "\<And>us::('b,string) term list. length us=length modes \<Longrightarrow>
      (\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)) \<Longrightarrow>
      SN_on (lp_triple_calls (set (lp_dependency_triples (lp_roles_program p d Q)))
        (lp_roles_program p d Q))
        {(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
  shows "SN_on (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpp_return_root_sound[where p=p and d=d, OF checked len ground])
  fix us :: "('b,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  show "SN_on (lp_ild (lp_roles_program p d Q))
    {[(p (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)]}"
    by (rule lp_triple_calls_imply_source_termination[OF child[OF length gr]])
qed


definition lpp_return_action_parser where
  "lpp_return_action_parser =
    (xml_singleton (STR ''cut'') lpc_return_action_parser LPPRCut) XMLor
    (XMLdo (STR ''variableTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPRVar f a gs active saved yes no)}) XMLor
    (XMLdo (STR ''identityTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPRIdentity f a b gs active saved yes no)})"

fun lpp_var_template where
  "lpp_var_template (LPCAtom (Fun (LPCUser f) ts)) =
    ((f,length ts)\<notin>lpp_builtin_signature \<or> (lpp_var_name f \<and> length ts=1) \<or> (lpp_identity_name f \<and> length ts=2))"
| "lpp_var_template (LPCAtom _) = False"
| "lpp_var_template (LPCMeta _) = False"
| "lpp_var_template (LPCExpand _ _) = False"
| "lpp_var_template _ = True"

definition lpp_var_source where
  "lpp_var_source P q modes =
    (((q,length modes)\<notin>lpp_builtin_signature \<or> (lpp_var_name q \<and> length modes=1) \<or> (lpp_identity_name q \<and> length modes=2)) \<and>
      list_all (\<lambda>c. list_all lpp_var_template (snd c)) P)"

definition check_lpp_return_triples where
  "check_lpp_return_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs =
    (lpp_return_check_root fuel P Q nds states returned arity acts r q modes \<and>
     (let p=lpc_lookup fallback predicates; d=lpc_lookup fallback constructors in
       R=lp_roles_program p d Q \<and> D=lp_dependency_triples R \<and>
       q' = p (lpcn_pred (nds!r)) \<and> n=length modes \<and> positions=lpc_positions modes \<and>
       check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs))"

theorem check_lpp_return_triples_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list" and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "check_lpp_return_triples I J fuel P Q nds states returned arity acts r q modes predicates constructors
      D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof (rule lpp_return_root_triples_sound[where p="lpc_lookup fallback predicates"
    and d="lpc_lookup fallback constructors", OF _ len ground])
  show "lpp_return_check_root fuel P Q nds states returned arity acts r q modes"
    using ok by (simp add: check_lpp_return_triples_def)
next
  fix us :: "((string,nat list) lab,string) term list"
  assume length: "length us=length modes"
    and gr: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (us!i)"
  have child: "check_lp_triple_pidp I J D R outs fallback dnames pnames marks filters q' n positions labs proofs"
    using ok by (auto simp: check_lpp_return_triples_def Let_def)
  have "SN_on (lp_triple_calls (set D) R) {(q',map (\<lambda>t. lp_ieval t LPIVar) us)}"
    by (rule check_lp_triple_pidp_sound[OF I J child])
      (use ok length gr in \<open>auto simp: check_lpp_return_triples_def Let_def\<close>)
  then show "SN_on (lp_triple_calls
      (set (lp_dependency_triples (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q)))
      (lp_roles_program (lpc_lookup fallback predicates) (lpc_lookup fallback constructors) Q))
      {(lpc_lookup fallback predicates (lpcn_pred (nds!r)),map (\<lambda>t. lp_ieval t LPIVar) us)}"
    using ok by (auto simp: check_lpp_return_triples_def Let_def)
qed

definition lpp_return_triples_parser where
  "lpp_return_triples_parser = XMLdo (STR ''prologVarReturnDependencyTriplesProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
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
    acts\<leftarrow>xml_many (STR ''actions'') lpp_return_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    enc_pred\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    enc_data\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (profile,P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,child)
  }"

definition check_lpp_return_triples_xml where
  "check_lpp_return_triples_xml xml = (case parse_xml_string lpp_return_triples_parser xml of
    Right (profile,P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and> lpp_var_source P q modes \<and>
      check_lpp_return_triples tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        D R outs fallback dnames pnames marks filters q' n positions labs proofs
    | _\<Rightarrow>False)"

theorem check_lpp_return_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_return_triples_parser xml =
    Right (profile,P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpp_return_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpp_return_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>auto simp: check_lpp_return_triples_xml_def\<close>)

corollary check_lpp_return_triples_xml_uncaught_errors:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_return_triples_parser xml =
    Right (profile,P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpp_return_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_prolog_stop_extension
    (lpp_atomic_source P lpp_builtin_signature lpp_test_builtin) E)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule lpp_atomic_uncaught_errors)
    (rule check_lpp_return_triples_xml_sound[OF parsed ok len ground])

end
