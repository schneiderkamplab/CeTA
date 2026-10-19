theory Higher_Order_Filtered_Order
  imports "Higher_Order_CeTA_Semantic.Higher_Order_CeTA_Semantic_Check"
begin

definition ho_selected_arguments :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ho_selected_arguments indices xs = map ((!) xs) (filter (\<lambda>i. i<length xs) indices)"

lemma ho_selected_arguments_map:
  "ho_selected_arguments indices (map f xs) = map f (ho_selected_arguments indices xs)"
  unfolding ho_selected_arguments_def
  by (auto simp: map_map intro!: map_cong)

lemma ho_selected_arguments_set:
  "set (ho_selected_arguments indices xs) \<subseteq> set xs"
  unfolding ho_selected_arguments_def by (auto simp: in_set_conv_nth)

lemma ho_selected_arguments_update:
  assumes "i<length xs" "(y,xs!i)\<in>r"
  shows "ho_selected_arguments indices (xs[i:=y]) = ho_selected_arguments indices xs \<or>
    (ho_selected_arguments indices (xs[i:=y]),ho_selected_arguments indices xs)\<in>lex r"
  using assms
  by (induction indices) (auto simp: ho_selected_arguments_def nth_list_update split: if_splits)

definition ho_filtered_less where
  "ho_filtered_less priority select phase d ys c xs =
    (ho_lex_subterm (ho_selected_arguments (select d) ys) (ho_selected_arguments (select c) xs) \<or>
      (ho_selected_arguments (select d) ys = ho_selected_arguments (select c) xs \<and>
        (phase d < phase c \<or> (phase d = phase c \<and>
          ho_lex_subterm (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)))))"

context ho_source_neutral_reducibility
begin

definition filtered_call_order :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    (nat \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    ((nat \<times> ho_term list) \<times> (nat \<times> ho_term list)) set" where
  "filtered_call_order ranks priority select phase =
    inv_image (less_than <*lex*> (lex (terminating_descent\<^sup>+) <*lex*>
      (less_than <*lex*> lex (terminating_descent\<^sup>+))))
    (\<lambda>(c,xs). (ranks c, ho_selected_arguments (select c) xs,
      phase c, ho_priority_arguments priority xs))"

lemma wf_filtered_call_order:
  "wf (filtered_call_order ranks priority select phase)"
  unfolding filtered_call_order_def
  by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_terminating_descent)

lemma argument_step_filtered_call_order:
  assumes args: "list_all2 source.computable Ts xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>filtered_call_order ranks priority select phase"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain A where cv: "source.computable A v"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have small: "(w,v)\<in>terminating_descent"
    using computable_application_descent[OF cv] vw
    by (simp add: terminating_descent_def application_descent_def)
  have index: "length us<length xs" and at: "xs!length us=v"
    and update: "ys=xs[length us:=w]"
    by (simp_all add: xs ys list_update_append)
  have selected: "ho_selected_arguments (select c) ys = ho_selected_arguments (select c) xs \<or>
      (ho_selected_arguments (select c) ys,ho_selected_arguments (select c) xs)\<in>lex (terminating_descent\<^sup>+)"
    unfolding update
    by (rule ho_selected_arguments_update[OF index]) (use r_into_trancl[OF small] at in simp)
  have full: "(ho_priority_arguments priority ys,ho_priority_arguments priority xs)\<in>lex (terminating_descent\<^sup>+)"
    using argument_step_priority_call_order[where rank=ranks and priority=priority and c=c, OF args step]
    by (simp add: priority_call_order_def inv_image_def lex_prod_def)
  show ?thesis using selected full
    by (auto simp: filtered_call_order_def inv_image_def lex_prod_def)
qed

lemma syntactic_filtered_call_order:
  assumes checked: "ho_filtered_less priority select phase d ys c xs"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_open s b 0 x)"
    and ranks: "ranks d=ranks c"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>filtered_call_order ranks priority select phase"
proof -
  have filtered:
    "(map (ho_open s b 0) (ho_selected_arguments (select d) ys),
      map (ho_open s b 0) (ho_selected_arguments (select c) xs))\<in>lex (terminating_descent\<^sup>+)"
    if "ho_lex_subterm (ho_selected_arguments (select d) ys) (ho_selected_arguments (select c) xs)"
  proof -
    have "((d,map (ho_open s b 0) (ho_selected_arguments (select d) ys)),
      (c,map (ho_open s b 0) (ho_selected_arguments (select c) xs)))\<in>call_order ranks"
      by (rule syntactic_lex_open_call_order[where rank=ranks and s=s and b=b and c=c and d=d,
        OF that _ ranks]) (use acc ho_selected_arguments_set in blast)
    then show ?thesis using ranks by (simp add: call_order_def inv_image_def lex_prod_def)
  qed
  have full:
    "(map (ho_open s b 0) (ho_priority_arguments priority ys),
      map (ho_open s b 0) (ho_priority_arguments priority xs))\<in>lex (terminating_descent\<^sup>+)"
    if "ho_lex_subterm (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)"
    using syntactic_priority_call_order[where s=s and b=b and rank=ranks and c=c and d=d,
      OF that acc ranks] ranks
    by (simp add: priority_call_order_def inv_image_def lex_prod_def ho_priority_arguments_map)
  show ?thesis using checked ranks filtered full
    by (auto simp: ho_filtered_less_def filtered_call_order_def inv_image_def lex_prod_def
      ho_selected_arguments_map ho_priority_arguments_map)
qed

end
end
