theory Higher_Order_Semantic_Call_Order
  imports Higher_Order_Ordered_Recursion
begin

context ho_source_accessible_reducibility
begin

definition semantic_call_order :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> ho_term list \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> ((nat \<times> ho_term list) \<times> (nat \<times> ho_term list)) set" where
  "semantic_call_order prec weight priority =
    inv_image (less_than <*lex*> (less_than <*lex*> lex (terminating_descent\<^sup>+)))
      (\<lambda>(c,xs). ((prec c::nat),(weight c xs::nat),ho_priority_arguments priority xs))"

lemma wf_semantic_call_order: "wf (semantic_call_order prec weight priority)"
  unfolding semantic_call_order_def
  by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_terminating_descent)

lemma semantic_argument_step_order:
  assumes args: "list_all2 source_candidate Ts xs" and step: "ho_arguments_step S V R B xs ys"
    and weak: "weight c ys\<le>weight c xs"
  shows "((c,ys),(c,xs))\<in>semantic_call_order prec weight priority"
proof -
  have syntactic: "((c,ys),(c,xs))\<in>priority_call_order prec priority"
    by (rule candidate_argument_step_order[OF args step])
  have lex: "(ho_priority_arguments priority ys,ho_priority_arguments priority xs)\<in>lex (terminating_descent\<^sup>+)"
    using syntactic by (simp add: priority_call_order_def inv_image_def lex_prod_def)
  show ?thesis using lex weak
    by (auto simp: semantic_call_order_def inv_image_def lex_prod_def)
qed

lemma semantic_strict_call_order:
  "prec d=prec c \<Longrightarrow> weight d ys<weight c xs \<Longrightarrow>
    ((d,ys),(c,xs))\<in>semantic_call_order prec weight priority"
  by (simp add: semantic_call_order_def inv_image_def lex_prod_def)

lemma semantic_syntactic_call_order:
  assumes lex: "ho_lex_subterm (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_open s b 0 x)"
    and prec: "prec d=prec c"
    and weak: "weight d (map (ho_open s b 0) ys)\<le>weight c (map (ho_open s b 0) xs)"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>semantic_call_order prec weight priority"
proof -
  have syntactic: "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>priority_call_order prec priority"
    by (rule syntactic_priority_call_order[where rank=prec and c=c and d=d, OF lex acc prec])
  show ?thesis using syntactic prec weak
    by (auto simp: priority_call_order_def semantic_call_order_def inv_image_def lex_prod_def)
qed

end

end
