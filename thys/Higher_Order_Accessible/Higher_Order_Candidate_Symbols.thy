theory Higher_Order_Candidate_Symbols
  imports Higher_Order_Candidate_Prefix
begin

abbreviation ho_source_candidate_computable where
  "ho_source_candidate_computable S V R B rank \<equiv>
    ho_reducibility.candidate_computable (ho_step S V R B) HApp
      (\<lambda>A t. ho_typeof S V B t=Some A)
      (ho_accessible_reducibility.accessible_candidates (ho_step S V R B) HApp
        (\<lambda>A t. ho_typeof S V B t=Some A) rank (ho_accessible_arguments rank S V B))"

theorem ho_candidate_symbols_imply_SN:
  assumes zero: "ho_zero_arity_rules R"
    and heads: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow>
      \<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    and finite_sorts: "finite K"
    and symbols: "\<And>W n T. (\<And>b. b\<in>K \<Longrightarrow> HBase b\<in>set W) \<Longrightarrow> ho_lookup S n=Some T \<Longrightarrow>
      ho_source_candidate_computable S W R [] rank T (HConst n)"
    and ty: "ho_typeof S V [] t=Some A"
  shows "Wellfounded.accp (\<lambda>u t. ho_step S V R [] t u) t"
proof -
  let ?K = "K \<union> (\<Union>T\<in>ho_binder_types t. ho_type_bases T)"
  let ?extra = "map HBase (sorted_list_of_set ?K)"
  let ?W = "V@?extra"
  interpret ext: ho_source_accessible_reducibility S ?W R "[]" rank
    by unfold_locales (rule zero, rule heads, assumption)
  have finite: "finite ?K" using finite_sorts by simp
  have available: "HBase b\<in>set ?W" if "b\<in>K" for b
    using that finite by simp
  have inhabited: "\<exists>x. ext.source_candidate T x" if tm: "T\<in>ho_binder_types t" for T
  proof (rule ext.source_candidate_type_inhabited)
    fix b assume "b\<in>ho_type_bases T"
    then have bk: "b\<in>?K" using tm by blast
    have mem: "HBase b\<in>set ?W" using bk finite by simp
    then obtain n where n: "n<length ?W" and eq: "?W!n=HBase b" by (metis in_set_conv_nth)
    have "ext.source_candidate (HBase b) (HFree n)"
      by (rule ext.source_candidate_free) (use n eq in auto)
    then show "\<exists>x. ext.source_candidate (HBase b) x" by blast
  qed
  have tt: "ho_typeof S ?W [] t=Some A" by (rule ho_typeof_extend_free[OF ty])
  have ct: "ext.source_candidate A t"
    by (rule ext.source_candidate_constants_suffice[OF tt symbols[OF available] inhabited])
  show ?thesis by (rule ho_SN_restrict_free[OF ext.source.candidate_SN[OF ct]])
qed

theorem ho_candidate_symbol_termination:
  assumes zero: "ho_zero_arity_rules R"
    and heads: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow>
      \<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    and finite_sorts: "finite K"
    and symbols: "\<And>W n T. (\<And>b. b\<in>K \<Longrightarrow> HBase b\<in>set W) \<Longrightarrow> ho_lookup S n=Some T \<Longrightarrow>
      ho_source_candidate_computable S W R [] rank T (HConst n)"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have acc: "Wellfounded.accp (\<lambda>u t. (t,u)\<in>ho_relation S V R A) t" for t
  proof (cases "ho_typeof S V [] t=Some A")
    case True
    have sn: "Wellfounded.accp (\<lambda>u t. ho_step S V R [] t u) t"
      by (rule ho_candidate_symbols_imply_SN[OF zero heads finite_sorts symbols True])
    have sub: "(\<lambda>u t. (t,u)\<in>ho_relation S V R A)\<le>(\<lambda>u t. ho_step S V R [] t u)"
      by (auto simp: ho_relation_def)
    show ?thesis using accp_subset[OF sub] sn by blast
  next
    case False
    show ?thesis by (rule accp.accI) (use False in \<open>auto simp: ho_relation_def\<close>)
  qed
  have "wfp (\<lambda>u t. (t,u)\<in>ho_relation S V R A)" by (rule accp_wfpI) (simp add: acc)
  then show ?thesis by (simp add: wfp_def converse_def)
qed

end
