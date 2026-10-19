theory Higher_Order_First_Order_Delegation
  imports Higher_Order_Algebraic_Simulation
begin

context ho_source_neutral_reducibility
begin

text \<open>First-order termination is transferred to the original
higher-order relation, including beta steps in arguments. The extracted
relation must contain every algebraic rule instance and the two choice
projections, and must be closed under arbitrary first-order contexts.
Termination of an innermost-only fragment is insufficient for this theorem.\<close>

theorem ho_first_order_delegation_SN:
  fixes F :: "nat set" and arity :: "nat \<Rightarrow> nat" and ce :: nat
    and rel :: "ho_fo_tree \<Rightarrow> ho_fo_tree \<Rightarrow> bool"
  assumes rule_arities: "\<And>G l r c. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst c \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity c"
    and branching: "\<And>t. finite {u. ho_step S V R B t u}"
    and ce_left: "\<And>x y. rel (HFOFun ce [x,y]) x"
    and ce_right: "\<And>x y. rel (HFOFun ce [x,y]) y"
    and fo_context: "\<And>c xs ys x y. rel x y \<Longrightarrow>
      rel (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
    and coverage: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p \<and> (p,q)\<in>P"
    and instances: "\<And>p q s. (p,q)\<in>P \<Longrightarrow>
      rel (ho_fo_substitution s p) (ho_fo_substitution s q)"
    and fo_wf: "wf {(u,t). rel\<^sup>+\<^sup>+ t u}"
    and safe: "ho_projection_safe F arity t"
  shows "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t"
proof (rule ho_safe_context_SN[where rel=rel and ce=ce,
    OF rule_arities branching ce_left ce_right fo_context _ fo_wf safe])
  fix x y c
  assume sx: "ho_projection_safe F arity x" and node: "ho_fo_node F arity x=Some c"
    and root: "ho_root_step S V R B x y"
  show "ho_projection_safe F arity y \<and>
    rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce x) (ho_context_projection F arity ce y)"
    by (rule ho_algebraic_root_simulation[where P=P and rel=rel,
          OF sx node root coverage instances])
qed

lemma ho_first_order_call_safe:
  assumes member: "c\<in>F" and len: "length xs=arity c"
    and args: "\<And>x. x\<in>set xs \<Longrightarrow>
      Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) x"
  shows "ho_projection_safe F arity (ho_apply_terms (HConst c) xs)"
proof -
  have node: "ho_fo_node F arity (ho_apply_terms (HConst c) xs)=Some c"
    by (rule ho_fo_node_call) (rule member, rule len)
  have safe: "list_all (ho_projection_safe F arity) xs"
    unfolding list_all_iff
    by (intro ballI ho_projection_safe_SN source_SN_application_descent args)
  show ?thesis using ho_projection_safe.simps[of F arity "ho_apply_terms (HConst c) xs"]
    by (simp only: node option.simps ho_apply_terms_arguments ho_spine_arguments.simps append.simps safe)
qed

end
end
