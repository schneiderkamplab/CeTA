theory LP_Cut_Uniform_Recursion_XML
  imports LP_Cut_Uniform_Recursion LP_Cut_NO_XML
begin

definition lpc_uniform_check where
  "lpc_uniform_check P q modes c xs us argv =
    (length modes=length xs \<and> length argv=length xs \<and> list_all ground argv \<and>
     c<length P \<and> distinct xs \<and> length us=length xs \<and>
     vars_term (Fun (LPCUser q) us) \<subseteq> set xs \<and>
     P!c=(Fun (LPCUser q) (map Var xs),[LPCAtom (Fun (LPCUser q) us)]) \<and>
     (case lp_cut_slice P (LPCUser q) (length xs) of [] \<Rightarrow> False | d#remaining \<Rightarrow> d=c))"

lemma lpc_uniform_check_sound:
  assumes checked: "lpc_uniform_check P q modes c xs us argv"
  shows "length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lp_cut_mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  obtain cs where first: "lp_cut_slice P (LPCUser q) (length xs)=c#cs"
    using checked by (auto simp: lpc_uniform_check_def split: list.splits)
  obtain rho where valuation: "map rho xs=map (\<lambda>t. lp_ieval t LPIVar) argv"
    using lpc_uniform_values[of xs "map (\<lambda>t. lp_ieval t LPIVar) argv"] checked
    by (auto simp: lpc_uniform_check_def)
  have grounds: "\<forall>x\<in>set xs. lp_seg_ground (rho x)"
  proof -
    have "\<forall>t\<in>set argv. lp_seg_ground (lp_ieval t LPIVar)"
      using checked by (auto simp: lpc_uniform_check_def list_all_iff ground_vars_term_empty
        intro!: lpc_uniform_ground_eval)
    then have "\<forall>v\<in>set (map rho xs). lp_seg_ground v" unfolding valuation by auto
    then show ?thesis by auto
  qed
  have no: "\<not>SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser q) (map Var xs)) rho)]]}"
    by (rule lpc_uniform_recursion_nontermination[OF first])
      (use checked grounds in \<open>auto simp: lpc_uniform_check_def\<close>)
  show ?thesis using checked no valuation
    by (simp add: lpc_uniform_check_def o_def)
qed

definition lpc_uniform_parser where
  "lpc_uniform_parser = XMLdo (STR ''lpCutUniformRecursionProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,body)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    c\<leftarrow>xml_nat (STR ''clause'');
    xs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    us\<leftarrow>xml_many (STR ''callArguments'') lpc_term_parser id;
    argv\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
    xml_return (P,q,modes,c,xs,us,argv)}"

definition check_lpc_uniform_xml where
  "check_lpc_uniform_xml xml = (case parse_xml_string lpc_uniform_parser xml of
    Right (P,q,modes,c,xs,us,argv) \<Rightarrow> lpc_uniform_check P q modes c xs us argv
    | _ \<Rightarrow> False)"

theorem check_lpc_uniform_xml_sound:
  assumes "parse_xml_string lpc_uniform_parser xml = Right (P,q,modes,c,xs,us,argv)"
    "check_lpc_uniform_xml xml"
  shows "length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lp_cut_mgu_source P)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
  by (rule lpc_uniform_check_sound) (use assms in \<open>simp add: check_lpc_uniform_xml_def\<close>)

end
