theory Higher_Order_Definition_Expansion
  imports Higher_Order_Spine_Expansion
begin

text \<open>Source-bound expansion of a constant-headed call. The expansion
must simulate every possible original prefix-rule contraction; selecting one
successful rewrite is insufficient. Arguments need normalization, and only
the positively accessible ones additionally need computability.\<close>

context ho_source_accessible_reducibility
begin

theorem source_candidate_call_expansion:
  assumes initial: "P xs"
    and sn: "\<And>ys x. P ys \<Longrightarrow> x\<in>set ys \<Longrightarrow> source.strongly_normalizing x"
    and typed: "\<And>ys. P ys \<Longrightarrow>
      ho_typeof S V B (ho_apply_terms (HConst c) ys)=Some (HBase b)"
    and accessible: "\<And>ys A x. P ys \<Longrightarrow>
      (A,x)\<in>ho_accessible_arguments rank S V B (ho_apply_terms (HConst c) ys) \<Longrightarrow>
      source_candidate A x"
    and invariant: "\<And>ys zs. P ys \<Longrightarrow> ho_arguments_step S V R B ys zs \<Longrightarrow> P zs"
    and roots: "\<And>ys ps qs u. P ys \<Longrightarrow> ys=ps@qs \<Longrightarrow>
      ho_root_step S V R B (ho_apply_terms (HConst c) ps) u \<Longrightarrow>
      (ho_step S V R B)\<^sup>*\<^sup>* (ho_apply_terms e ys) (ho_apply_terms u qs)"
    and expanded: "source_candidate (HBase b) (ho_apply_terms e xs)"
  shows "source_candidate (HBase b) (ho_apply_terms (HConst c) xs)"
proof -
  have all: "P ys \<longrightarrow> source_candidate (HBase b) (ho_apply_terms e ys) \<longrightarrow>
      source_candidate (HBase b) (ho_apply_terms (HConst c) ys)" for ys
  proof (induction ys rule: wf_induct[OF wf_lex[OF wf_trancl[OF wf_terminating_descent]]])
    case (1 ys)
    show ?case
    proof (intro impI)
      assume p: "P ys" and comp: "source_candidate (HBase b) (ho_apply_terms e ys)"
      have reducts: "source_candidate (HBase b) u"
        if st: "ho_step S V R B (ho_apply_terms (HConst c) ys) u" for u
      proof -
        from source_call_prefix_reduct[OF st] show ?thesis
        proof (elim disjE exE conjE)
          fix ps qs v assume ys: "ys=ps@qs"
            and root: "ho_root_step S V R B (ho_apply_terms (HConst c) ps) v"
            and eq: "u=ho_apply_terms v qs"
          show ?thesis unfolding eq
            by (rule source_candidate_reductions[OF roots[OF p ys root] comp])
        next
          fix zs assume step: "ho_arguments_step S V R B ys zs"
            and eq: "u=ho_apply_terms (HConst c) zs"
          have order: "((0,zs),(0,ys))\<in>call_order (\<lambda>_. 0)"
            by (rule sn_argument_step_order[OF sn[OF p] step])
          have small: "(zs,ys)\<in>lex (terminating_descent\<^sup>+)"
            using order by (simp add: call_order_def inv_image_def lex_prod_def)
          have p': "P zs" by (rule invariant[OF p step])
          have cc: "source_candidate (HBase b) (ho_apply_terms e zs)"
            by (rule source_candidate_reduction[OF comp ho_expansion_argument_step[OF step]])
          show ?thesis unfolding eq using 1 small p' cc by blast
        qed
      qed
      show "source_candidate (HBase b) (ho_apply_terms (HConst c) ys)"
        by (rule source_candidate_base_intro[OF typed[OF p] reducts accessible[OF p]])
    qed
  qed
  show ?thesis using all[of xs] initial expanded by blast
qed

end
end
