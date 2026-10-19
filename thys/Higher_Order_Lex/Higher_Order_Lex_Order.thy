theory Higher_Order_Lex_Order
  imports "Higher_Order_Meta.Higher_Order_Meta_Checker"
begin

definition ho_nat_lex_weak where
  "ho_nat_lex_weak xs ys \<longleftrightarrow> xs=ys \<or> (xs,ys)\<in>lex (less_than::(nat\<times>nat)set)"

lemma ho_nat_lex_cons:
  "length xs=length ys \<Longrightarrow> x\<le>y \<Longrightarrow>
    (x<y \<or> (xs,ys)\<in>lex less_than) \<Longrightarrow>
    (x#xs,y#ys)\<in>lex (less_than::(nat\<times>nat)set)"
  by auto

lemma ho_nat_lex_weak_cons:
  "x\<le>y \<Longrightarrow> ho_nat_lex_weak xs ys \<Longrightarrow> ho_nat_lex_weak (x#xs) (y#ys)"
  unfolding ho_nat_lex_weak_def
  by (auto simp: lexord_lex)

lemma ho_pointwise_nat_lex:
  "list_all2 (\<le>) xs ys \<Longrightarrow> ho_nat_lex_weak xs ys"
  by (induction rule: list_all2_induct)
     (simp add: ho_nat_lex_weak_def, rule ho_nat_lex_weak_cons, assumption, assumption)

context ho_source_accessible_reducibility
begin

definition lex_semantic_call_order :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> ho_term list \<Rightarrow> nat list) \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> ((nat \<times> ho_term list) \<times> (nat \<times> ho_term list)) set" where
  "lex_semantic_call_order prec weight priority =
    inv_image (less_than <*lex*> (lex less_than <*lex*> lex (terminating_descent\<^sup>+)))
      (\<lambda>(c,xs). (prec c,weight c xs,ho_priority_arguments priority xs))"

lemma wf_lex_semantic_call_order: "wf (lex_semantic_call_order prec weight priority)"
  unfolding lex_semantic_call_order_def
  by (intro wf_inv_image wf_lex_prod wf_less_than wf_lex wf_trancl wf_terminating_descent)

lemma lex_semantic_argument_step_order:
  assumes args: "list_all2 source_candidate Ts xs" and step: "ho_arguments_step S V R B xs ys"
    and weak: "ho_nat_lex_weak (weight c ys) (weight c xs)"
  shows "((c,ys),(c,xs))\<in>lex_semantic_call_order prec weight priority"
proof -
  have syntactic: "((c,ys),(c,xs))\<in>priority_call_order prec priority"
    by (rule candidate_argument_step_order[OF args step])
  show ?thesis using syntactic weak
    by (auto simp: priority_call_order_def lex_semantic_call_order_def ho_nat_lex_weak_def inv_image_def lex_prod_def)
qed

lemma lex_semantic_strict_call_order:
  "prec d=prec c \<Longrightarrow> (weight d ys,weight c xs)\<in>lex less_than \<Longrightarrow>
    ((d,ys),(c,xs))\<in>lex_semantic_call_order prec weight priority"
  by (simp add: lex_semantic_call_order_def inv_image_def lex_prod_def)

lemma lex_semantic_syntactic_call_order:
  assumes lexical: "ho_lex_subterm (ho_priority_arguments priority ys) (ho_priority_arguments priority xs)"
    and acc: "\<And>x. x\<in>set xs \<Longrightarrow> Wellfounded.accp application_descent (ho_open s b 0 x)"
    and prec: "prec d=prec c"
    and weak: "ho_nat_lex_weak (weight d (map (ho_open s b 0) ys)) (weight c (map (ho_open s b 0) xs))"
  shows "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>lex_semantic_call_order prec weight priority"
proof -
  have syntactic: "((d,map (ho_open s b 0) ys),(c,map (ho_open s b 0) xs))\<in>priority_call_order prec priority"
    by (rule syntactic_priority_call_order[where rank=prec and c=c and d=d, OF lexical acc prec])
  show ?thesis using syntactic prec weak
    by (auto simp: priority_call_order_def lex_semantic_call_order_def ho_nat_lex_weak_def inv_image_def lex_prod_def)
qed


end

definition ho_lex_weights where
  "ho_lex_weights S V B orders e c xs=map (\<lambda>(ps,ms).
    ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e c xs) orders"

definition ho_lex_signatures where
  "ho_lex_signatures S orders=list_all (\<lambda>(ps,ms).
    ho_check_polynomial_signature S ps \<and> ho_check_polynomial_signature S ms) orders"

fun ho_check_lex_comparison where
  "ho_check_lex_comparison S [] fuel G c ls d xs strict=(\<not>strict)"
| "ho_check_lex_comparison S ((ps,ms)#orders) fuel G c ls d xs strict=
    (ho_check_call_comparison S ps ms fuel G c ls d xs False \<and>
      (if strict then ho_check_call_comparison S ps ms fuel G c ls d xs True \<or>
          ho_check_lex_comparison S orders fuel G c ls d xs True
       else ho_check_lex_comparison S orders fuel G c ls d xs False))"

theorem ho_check_lex_comparison_sound:
  assumes signatures: "ho_lex_signatures S orders"
    and checked: "ho_check_lex_comparison S orders fuel G c ls d xs strict"
    and subst: "ho_typed_subst S V B G s" and ev: "ho_env_value (B@V) e"
  shows "if strict then
    (ho_lex_weights S V B orders e d (map (ho_open s b 0) xs),
     ho_lex_weights S V B orders e c (map (ho_subst s 0) ls))\<in>lex less_than
    else ho_nat_lex_weak (ho_lex_weights S V B orders e d (map (ho_open s b 0) xs))
      (ho_lex_weights S V B orders e c (map (ho_subst s 0) ls))"
using signatures checked
proof (induction orders arbitrary: strict)
  case Nil
  then show ?case by (simp add: ho_lex_weights_def ho_nat_lex_weak_def)
next
  case (Cons pair orders)
  obtain ps ms where pair: "pair=(ps,ms)" by (cases pair) auto
  have ps: "ho_check_polynomial_signature S ps" and ms: "ho_check_polynomial_signature S ms"
    and rest: "ho_lex_signatures S orders" using Cons.prems(1) by (simp_all add: pair ho_lex_signatures_def)
  have weak: "ho_check_call_comparison S ps ms fuel G c ls d xs False" using Cons.prems(2) by (simp add: pair)
  let ?x = "ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e d (map (ho_open s b 0) xs)"
  let ?y = "ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e c (map (ho_subst s 0) ls)"
  have le: "?x\<le>?y" using ho_check_call_comparison_sound[where b=b, OF ps ms weak subst ev] by simp
  show ?case
  proof (cases strict)
    case False
    have ck: "ho_check_lex_comparison S orders fuel G c ls d xs False" using Cons.prems(2) False by (simp add: pair)
    show ?thesis using ho_nat_lex_weak_cons[OF le] Cons.IH[OF rest ck]
      by (simp add: False pair ho_lex_weights_def)
  next
    case True
    have decrease: "?x<?y \<or>
        (ho_lex_weights S V B orders e d (map (ho_open s b 0) xs),
         ho_lex_weights S V B orders e c (map (ho_subst s 0) ls))\<in>lex less_than"
      using Cons.prems(2) True ho_check_call_comparison_sound[where b=b, OF ps ms _ subst ev]
        Cons.IH[OF rest, of True] by (auto simp: pair)
    show ?thesis using ho_nat_lex_cons[OF _ le decrease]
      by (simp add: True pair ho_lex_weights_def)
  qed
qed

lemma ho_lex_weights_step:
  assumes valid: "ho_lex_signatures S orders" and zero: "ho_zero_arity_rules R"
    and ev: "ho_env_value (B@V) e"
    and weak: "\<And>ps ms G l r. (ps,ms)\<in>set orders \<Longrightarrow> (G,l,r)\<in>set R \<Longrightarrow>
      ho_weak_rule S (ho_polynomial_interpretation ps) G l r"
    and symbol: "ho_lookup S c=Some A" and bound: "n\<le>length (ho_argument_types A)"
    and args: "list_all2 (\<lambda>T x. ho_typeof S V B x=Some T) (take n (ho_argument_types A)) xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_nat_lex_weak (ho_lex_weights S V B orders e c ys) (ho_lex_weights S V B orders e c xs)"
proof -
  have le: "ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e c ys\<le>
      ho_call_weight S V B (ho_polynomial_interpretation ps) (ho_polynomial_interpretation ms) e c xs"
    if member: "(ps,ms)\<in>set orders" for ps ms
  proof -
    have ps: "ho_check_polynomial_signature S ps" and ms: "ho_check_polynomial_signature S ms"
      using valid member by (auto simp: ho_lex_signatures_def list_all_iff)
    show ?thesis by (rule ho_call_weight_step[OF zero ho_polynomial_signature_closed[OF ps]
      ho_polynomial_signature_value[OF ps] ho_polynomial_signature_value[OF ms] ev
      weak[OF member] symbol bound args step])
  qed
  have pointwise: "list_all2 (\<le>) (ho_lex_weights S V B orders e c ys) (ho_lex_weights S V B orders e c xs)"
    unfolding ho_lex_weights_def using le
    by (induction orders) (auto split: prod.splits)
  show ?thesis by (rule ho_pointwise_nat_lex[OF pointwise])
qed

end
