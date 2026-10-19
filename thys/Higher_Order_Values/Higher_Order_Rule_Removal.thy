theory Higher_Order_Rule_Removal
  imports Higher_Order_Values
begin

text \<open>Modular rule removal keeps the complete typed rewrite relation,
including beta, in the residual obligation. A weak step must either decrease
the semantic measure or belong to that independently proved residual.\<close>

lemma ho_measure_residual_termination:
  fixes f :: "'a \<Rightarrow> nat"
  assumes residual: "wf (Q\<inverse>)"
    and weak: "\<And>t u. (t,u)\<in>R \<Longrightarrow> f u\<le>f t"
    and equal: "\<And>t u. (t,u)\<in>R \<Longrightarrow> f u=f t \<Longrightarrow> (t,u)\<in>Q"
  shows "wf (R\<inverse>)"
proof -
  have wf: "wf (inv_image (less_than <*lex*> (Q\<inverse>)) (\<lambda>t. (f t,t)))"
    by (rule wf_inv_image) (rule wf_lex_prod[OF wf_less_than residual])
  show ?thesis
  proof (rule wf_subset[OF wf], rule subsetI)
    fix p assume "p\<in>R\<inverse>"
    then obtain u t where p: "p=(u,t)" and edge: "(t,u)\<in>R" by auto
    have cases: "f u<f t \<or> f u=f t" using weak[OF edge] by arith
    have "f u=f t \<Longrightarrow> (t,u)\<in>Q" by (rule equal[OF edge])
    then show "p\<in>inv_image (less_than <*lex*> (Q\<inverse>)) (\<lambda>t. (f t,t))"
      using cases p by (auto simp: inv_image_def lex_prod_def)
  qed
qed

theorem ho_typed_rule_removal:
  assumes residual: "wf ((ho_relation S V R' A)\<inverse>)"
    and weak: "\<And>t u. (t,u)\<in>ho_relation S V R A \<Longrightarrow>
      ho_observe T (I u)\<le>ho_observe T (I t)"
    and strict: "\<And>t u. (t,u)\<in>ho_relation S V R A \<Longrightarrow>
      (t,u)\<notin>ho_relation S V R' A \<Longrightarrow> ho_value_gt T (I t) (I u)"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof (rule ho_measure_residual_termination[where f="\<lambda>t. ho_observe T (I t)", OF residual weak])
  fix t u
  assume pair: "(t,u)\<in>ho_relation S V R A" and eq: "ho_observe T (I u)=ho_observe T (I t)"
  show "(t,u)\<in>ho_relation S V R' A"
  proof (rule ccontr)
    assume "(t,u)\<notin>ho_relation S V R' A"
    from ho_value_gt_observe[OF strict[OF pair this]] eq show False by simp
  qed
qed

end
