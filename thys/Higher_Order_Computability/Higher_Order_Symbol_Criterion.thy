theory Higher_Order_Symbol_Criterion
  imports Higher_Order_Source_Fundamental
begin

lemma ho_typeof_extend_free:
  "ho_typeof S V B t=Some A \<Longrightarrow> ho_typeof S (V@W) B t=Some A"
  by (induction t arbitrary: B A)
    (auto simp: nth_append split: option.splits ho_type.splits if_splits)

lemma ho_step_extend_free:
  "ho_step S V R B t u \<Longrightarrow> ho_step S (V@W) R B t u"
proof (induction rule: ho_step.induct)
  case (rule G l r B s t u)
  have subst: "ho_typed_subst S (V@W) B G s"
    using rule.hyps(3) ho_typeof_extend_free unfolding ho_typed_subst_def by blast
  show ?case by (rule ho_step.rule[OF rule.hyps(1,2) subst rule.hyps(4,5)])
next
  case (beta B A t u)
  show ?case by (rule ho_step.beta)
next
  case (app_left B t u x)
  show ?case by (rule ho_step.app_left[OF app_left.IH])
next
  case (app_right B t u x)
  show ?case by (rule ho_step.app_right[OF app_right.IH])
next
  case (abs A B t u)
  show ?case by (rule ho_step.abs[OF abs.IH])
qed

lemma ho_SN_restrict_free:
  "Wellfounded.accp (\<lambda>u t. ho_step S (V@W) R B t u) t \<Longrightarrow>
    Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t"
proof -
  have sub: "(\<lambda>u t. ho_step S V R B t u)\<le>(\<lambda>u t. ho_step S (V@W) R B t u)"
    using ho_step_extend_free by blast
  assume "Wellfounded.accp (\<lambda>u t. ho_step S (V@W) R B t u) t"
  then show ?thesis using accp_subset[OF sub] by blast
qed

lemma finite_ho_type_bases [simp]: "finite (ho_type_bases A)"
  by (induction A) auto

lemma finite_ho_binder_types [simp]: "finite (ho_binder_types t)"
  by (induction t) auto

abbreviation ho_source_computable where
  "ho_source_computable S V R B \<equiv> ho_reducibility.computable (ho_step S V R B) HApp
    (\<lambda>A t. ho_typeof S V B t=Some A)"

text \<open>Fresh variables only supply inhabitants of the finitely many base
sorts appearing in this term's binder annotations. Rewriting in the original
free-variable context embeds in the extended context, so normalization there
implies normalization of the original source term.\<close>

theorem ho_symbols_imply_SN:
  assumes zero: "ho_zero_arity_rules R"
    and heads: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow>
      \<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    and symbols: "\<And>W n T. ho_lookup S n=Some T \<Longrightarrow>
      ho_source_computable S W R [] T (HConst n)"
    and ty: "ho_typeof S V [] t=Some A"
  shows "Wellfounded.accp (\<lambda>u t. ho_step S V R [] t u) t"
proof -
  let ?K = "\<Union>T\<in>ho_binder_types t. ho_type_bases T"
  let ?extra = "map HBase (sorted_list_of_set ?K)"
  let ?W = "V@?extra"
  interpret ext: ho_source_neutral_reducibility S ?W R "[]"
    by unfold_locales (rule zero, rule heads, assumption)
  have finite: "finite ?K" by simp
  have inhabited: "\<exists>x. ext.source.computable T x" if tm: "T\<in>ho_binder_types t" for T
  proof (rule ext.source_type_inhabited)
    fix b assume "b\<in>ho_type_bases T"
    then have bk: "b\<in>?K" using tm by blast
    have mem: "HBase b\<in>set ?W" using bk finite by simp
    then obtain n where n: "n<length ?W" and eq: "?W!n=HBase b" by (metis in_set_conv_nth)
    have "ext.source.computable (HBase b) (HFree n)"
      by (rule ext.source_free_computable) (use n eq in auto)
    then show "\<exists>x. ext.source.computable (HBase b) x" by blast
  qed
  have tt: "ho_typeof S ?W [] t=Some A" by (rule ho_typeof_extend_free[OF ty])
  have ct: "ext.source.computable A t"
    by (rule ext.source_constants_suffice[OF tt symbols inhabited])
  show ?thesis by (rule ho_SN_restrict_free[OF ext.source.computable_SN[OF ct]])
qed

theorem ho_symbol_termination:
  assumes zero: "ho_zero_arity_rules R"
    and heads: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow>
      \<exists>c. ho_application_head (ho_erase_pattern l)=HConst c"
    and symbols: "\<And>W n T. ho_lookup S n=Some T \<Longrightarrow>
      ho_source_computable S W R [] T (HConst n)"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  have acc: "Wellfounded.accp (\<lambda>u t. (t,u)\<in>ho_relation S V R A) t" for t
  proof (cases "ho_typeof S V [] t=Some A")
    case True
    have sn: "Wellfounded.accp (\<lambda>u t. ho_step S V R [] t u) t"
      by (rule ho_symbols_imply_SN[OF zero heads symbols True])
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
