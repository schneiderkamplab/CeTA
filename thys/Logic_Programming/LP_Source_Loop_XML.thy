theory LP_Source_Loop_XML
  imports LP_Source_Loop LP_Source_Simplify_XML
begin

definition lp_source_loop_check where
  "lp_source_loop_check P q n positions c bindings =
    (c<length P \<and> fst (fst (P!c))=q \<and> length (snd (fst (P!c)))=n \<and>
     list_all (\<lambda>i. i<n) positions \<and> snd (P!c)\<noteq>[] \<and>
     list_all (\<lambda>(v,t). is_Var v) bindings \<and>
     (let subst = concat (map (\<lambda>(v,t). case v of Var x\<Rightarrow>[(x,t)] | _\<Rightarrow>[]) bindings)
      in hd (snd (P!c)) = lp_atom_subst (fst (P!c)) (\<lambda>x. the_default (Var x) (map_of subst x))))"

theorem lp_source_loop_check_sound:
  fixes P :: "('f,'v) lp_clause list" and seed :: 'f
  assumes ok: "lp_source_loop_check P q n positions c bindings"
  shows "\<exists>ts :: ('f,'v) term list. length ts=n \<and> list_all ground ts \<and>
    \<not>SN_on (lp_ld P) {[(q,ts)]} \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
proof -
  let ?h = "fst (P!c)"
  let ?subst = "concat (map (\<lambda>(v,t). case v of Var x\<Rightarrow>[(x,t)] | _\<Rightarrow>[]) bindings)"
  let ?tau = "\<lambda>x. the_default (Var x) (map_of ?subst x)"
  let ?rho = "\<lambda>x. Fun seed [] :: ('f,'v) term"
  let ?ts = "map (\<lambda>t. t\<cdot>?rho) (snd ?h)"
  have c: "c<length P" and pred: "fst ?h=q" and len: "length (snd ?h)=n"
    and nonempty: "snd (P!c)\<noteq>[]"
    and inst: "hd (snd (P!c))=lp_atom_subst ?h ?tau"
    using ok unfolding lp_source_loop_check_def Let_def by auto
  have body: "snd (P!c)=hd (snd (P!c))#tl (snd (P!c))" using nonempty by simp
  have finite: "\<not>SN_on (lp_ld P) {[(q,?ts)]}"
    using lp_head_instance_loop[OF c body inst, of ?rho]
    by (simp add: lp_atom_subst_def pred)
  have eval: "(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts) = lp_atom_eval ?h (\<lambda>x. LPIFun seed [])"
    using lp_atom_eval_finite_subst[of ?h ?rho LPIVar]
    by (simp only: lp_atom_subst_def lp_atom_eval_def fst_conv snd_conv pred lp_ieval.simps list.map)
  have infinite: "\<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)]}"
    unfolding eval by (rule lp_infinite_head_instance_loop[OF c body inst])
  have gr: "\<And>t :: ('f,'v) term. ground (t\<cdot>?rho)"
    by (simp add: ground_vars_term_empty vars_term_subst)
  show ?thesis by (rule exI[of _ ?ts]) (use finite infinite len gr in \<open>auto simp: list_all_iff\<close>)
qed

definition lp_source_loop_parser where
  "lp_source_loop_parser = XMLdo (STR ''lpTocl09SourceLoopProof'') {
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
    c \<leftarrow> xml_nat (STR ''clauseIndex'');
    seed \<leftarrow> xml_singleton (STR ''seed'') symbol_parser id;
    bindings \<leftarrow> xml_many (STR ''substitution'')
      (xml_pair (STR ''binding'') (CPF_Input_Parser.term symbol_parser Mapping.empty)
        (CPF_Input_Parser.term symbol_parser Mapping.empty) Pair) id;
    xml_return (P,query,c,seed,bindings)
  }"

definition check_lp_nontermination_xml where
  "check_lp_nontermination_xml xml = (case parse_xml_string lp_source_loop_parser xml of
    Right (P,(q,n,positions),c,seed,bindings) \<Rightarrow> lp_source_loop_check P q n positions c bindings
    | _\<Rightarrow>False)"

theorem check_lp_nontermination_xml_sound:
  assumes parsed: "parse_xml_string lp_source_loop_parser xml = Right (P,(q,n,positions),c,seed,bindings)"
    and ok: "check_lp_nontermination_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list. length ts=n \<and> list_all ground ts \<and>
    \<not>SN_on (lp_ld P) {[(q,ts)]} \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
  by (rule lp_source_loop_check_sound)
    (use parsed ok in \<open>simp add: check_lp_nontermination_xml_def\<close>)

end
