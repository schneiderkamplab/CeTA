theory Higher_Order_Priority_Order
  imports "Higher_Order_Computability.Higher_Order_Lambda_Schema"
begin

definition ho_priority_arguments :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ho_priority_arguments priority xs=map ((!) xs) (sort_key priority [0..<length xs])"

lemma ho_priority_arguments_map:
  "ho_priority_arguments priority (map f xs)=map f (ho_priority_arguments priority xs)"
  unfolding ho_priority_arguments_def by (auto simp: map_map intro!: map_cong)

lemma ho_priority_arguments_set [simp]:
  "set (ho_priority_arguments priority xs)=set xs"
  unfolding ho_priority_arguments_def by (auto simp: in_set_conv_nth)

lemma ho_priority_arguments_update:
  assumes i: "i<length xs" and edge: "(y,xs!i)\<in>r"
  shows "(ho_priority_arguments priority (xs[i:=y]), ho_priority_arguments priority xs)\<in>lex r"
proof -
  let ?is = "sort_key priority [0..<length xs]"
  have member: "i\<in>set ?is" using i by simp
  obtain pre post where split: "?is=pre@i#post" and absent: "i\<notin>set pre"
    using split_list_first[OF member] by blast
  have prefix: "map ((!) (xs[i:=y])) pre=map ((!) xs) pre"
  proof (rule map_cong)
    show "pre=pre" by simp
    fix j assume "j\<in>set pre"
    then have "i\<noteq>j" using absent by blast
    then show "xs[i:=y]!j=xs!j" by simp
  qed
  have ordered: "(map ((!) xs) pre @ y # map ((!) (xs[i:=y])) post,
      map ((!) xs) pre @ xs!i # map ((!) xs) post)\<in>lex r"
    using edge by (auto simp: lex_conv; blast)
  show ?thesis
    unfolding ho_priority_arguments_def
    by (simp only: length_list_update split map_append list.map nth_list_update_eq[OF i] prefix;
        rule ordered)
qed

context ho_source_neutral_reducibility
begin

definition priority_call_order :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    ((nat \<times> ho_term list) \<times> (nat \<times> ho_term list)) set" where
  "priority_call_order rank priority=inv_image (less_than <*lex*> lex (terminating_descent\<^sup>+))
    (\<lambda>(c,xs). (rank c,ho_priority_arguments priority xs))"

lemma wf_priority_call_order: "wf (priority_call_order rank priority)"
  unfolding priority_call_order_def
  by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_terminating_descent)

lemma argument_step_priority_call_order:
  assumes args: "list_all2 source.computable Ts xs" and step: "ho_arguments_step S V R B xs ys"
  shows "((c,ys),(c,xs))\<in>priority_call_order rank priority"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs" and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain A where cv: "source.computable A v"
    using args unfolding xs by (auto simp: list_all2_append2 list_all2_Cons2)
  have small: "(w,v)\<in>terminating_descent"
    using computable_application_descent[OF cv] vw
    by (simp add: terminating_descent_def application_descent_def)
  have index: "length us<length xs" and at: "xs!length us=v" and update: "ys=xs[length us:=w]"
    by (simp_all add: xs ys list_update_append)
  have lex: "(ho_priority_arguments priority ys,ho_priority_arguments priority xs)\<in>lex (terminating_descent\<^sup>+)"
    unfolding update by (rule ho_priority_arguments_update[OF index]) (use r_into_trancl[OF small] at in simp)
  show ?thesis using lex by (simp add: priority_call_order_def inv_image_def lex_prod_def)
qed

lemma syntactic_priority_call_order:
  assumes lex: "ho_lex_subterm (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_open s b 0 x)"
    and ranks: "rank d=rank c"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>priority_call_order rank priority"
proof -
  have arranged: "((d,map (ho_open s b 0) (ho_priority_arguments priority ys)),
      (c,map (ho_open s b 0) (ho_priority_arguments priority xs)))\<in>call_order rank"
    by (rule syntactic_lex_open_call_order[where rank=rank and s=s and b=b and c=c and d=d,
      OF lex _ ranks]) (use acc in simp)
  show ?thesis using arranged
    by (simp add: priority_call_order_def call_order_def inv_image_def ho_priority_arguments_map)
qed

end

end
