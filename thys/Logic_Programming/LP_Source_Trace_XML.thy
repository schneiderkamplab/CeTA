theory LP_Source_Trace_XML
  imports LP_Source_Trace LP_Source_Loop_XML
begin

definition lp_source_trace_check where
  "lp_source_trace_check P q n positions h steps bindings =
    (fst h=q \<and> length (snd h)=n \<and> list_all (\<lambda>i. i<n) positions \<and>
     steps\<noteq>[] \<and> (case lp_match_run P [h] steps of
       Some (b#bs) \<Rightarrow> b=lp_atom_subst h (lp_trace_subst bindings)
     | _ \<Rightarrow> False))"

theorem lp_source_trace_check_sound:
  fixes P :: "('f,'v) lp_clause list" and seed :: 'f
  assumes ok: "lp_source_trace_check P q n positions h steps bindings"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> list_all ground ts \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  obtain b bs where run: "lp_match_run P [h] steps=Some (b#bs)"
    and progress: "steps\<noteq>[]" and repeat: "b=lp_atom_subst h (lp_trace_subst bindings)"
    and pred: "fst h=q" and len: "length (snd h)=n"
    using ok unfolding lp_source_trace_check_def by (auto split: option.splits list.splits)
  let ?rho = "\<lambda>x. Fun seed [] :: ('f,'v) term"
  let ?ts = "map (\<lambda>t. t\<cdot>?rho) (snd h)"
  have eq: "(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts) = lp_atom_eval h (\<lambda>x. LPIFun seed [])"
    using lp_atom_eval_finite_subst[of h ?rho LPIVar]
    by (simp only: lp_atom_subst_def lp_atom_eval_def fst_conv snd_conv pred lp_ieval.simps list.map)
  have nontermination: "\<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)]}"
    unfolding eq by (rule lp_match_trace_loop[OF run progress repeat])
  have ground: "\<And>t :: ('f,'v) term. ground (t\<cdot>?rho)"
    by (simp add: ground_vars_term_empty vars_term_subst)
  show ?thesis by (rule exI[of _ ?ts])
    (use nontermination ground len in \<open>auto simp: list_all_iff\<close>)
qed

definition lp_trace_variable_parser where
  "lp_trace_variable_parser = xml_change (CPF_Input_Parser.term symbol_parser Mapping.empty)
    (\<lambda>t. case t of Var x \<Rightarrow> xml_return x
      | Fun _ _ \<Rightarrow> xml_error (STR ''Trace variable expected''))"

definition lp_trace_bindings_parser where
  "lp_trace_bindings_parser = xml_many (STR ''substitution'')
    (XMLdo (STR ''binding'') {
      x \<leftarrow> lp_trace_variable_parser;
      t \<leftarrow> CPF_Input_Parser.term symbol_parser Mapping.empty;
      xml_return (x,t)
    }) id"

definition lp_source_trace_parser where
  "lp_source_trace_parser = XMLdo (STR ''lpTocl09SourceTraceProof'') {
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
    seed \<leftarrow> xml_singleton (STR ''seed'') symbol_parser id;
    h \<leftarrow> xml_singleton (STR ''initial'') lp_atom_parser id;
    steps \<leftarrow> xml_many (STR ''steps'') (XMLdo (STR ''step'') {
      c \<leftarrow> xml_nat (STR ''clauseIndex'');
      bindings \<leftarrow> lp_trace_bindings_parser;
      xml_return (c,bindings)
    }) id;
    bindings \<leftarrow> lp_trace_bindings_parser;
    xml_return (P,query,seed,h,steps,bindings)
  }"

definition check_lp_source_trace_xml where
  "check_lp_source_trace_xml xml = (case parse_xml_string lp_source_trace_parser xml of
    Right (P,(q,n,positions),seed,h,steps,bindings) \<Rightarrow>
      lp_source_trace_check P q n positions h steps bindings
    | _ \<Rightarrow> False)"

theorem check_lp_source_trace_xml_sound:
  assumes parsed: "parse_xml_string lp_source_trace_parser xml =
    Right (P,(q,n,positions),seed,h,steps,bindings)"
    and ok: "check_lp_source_trace_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list. length ts=n \<and> list_all ground ts \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_source_trace_check_sound)
    (use parsed ok in \<open>simp add: check_lp_source_trace_xml_def\<close>)

definition check_lp_nontermination_full_xml where
  "check_lp_nontermination_full_xml xml =
    (check_lp_nontermination_xml xml \<or> check_lp_source_trace_xml xml)"

end
