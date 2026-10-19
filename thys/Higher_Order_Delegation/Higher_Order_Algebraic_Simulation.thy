theory Higher_Order_Algebraic_Simulation
  imports Higher_Order_Context_Simulation
begin

context ho_source_neutral_reducibility
begin

theorem ho_algebraic_root_simulation:
  fixes F :: "nat set" and arity :: "nat \<Rightarrow> nat" and ce :: nat
    and rel :: "ho_fo_tree \<Rightarrow> ho_fo_tree \<Rightarrow> bool"
  assumes safe: "ho_projection_safe F arity t"
    and node: "ho_fo_node F arity t=Some c"
    and step: "ho_root_step S V R B t u"
    and coverage: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow> d\<in>F \<Longrightarrow>
      \<exists>p q. l=ho_fo_pattern p \<and> r=ho_fo_pattern q \<and>
        ho_fo_wellformed F arity p \<and> ho_fo_wellformed F arity q \<and>
        ho_fo_variables q\<subseteq>ho_fo_variables p \<and> (p,q)\<in>P"
    and instances: "\<And>p q s. (p,q)\<in>P \<Longrightarrow>
      rel (ho_fo_substitution s p) (ho_fo_substitution s q)"
  shows "ho_projection_safe F arity u \<and>
    rel\<^sup>+\<^sup>+ (ho_context_projection F arity ce t) (ho_context_projection F arity ce u)"
proof -
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and li: "ho_instantiate s 0 l=Some t" and ri: "ho_instantiate s 0 r=Some u"
    using step unfolding ho_root_step_def by blast
  have head_t: "ho_application_head t=HConst c"
    using node unfolding ho_fo_node_def by (auto split: ho_term.splits if_splits)
  have head_l: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member li] head_t by simp
  obtain p q where l: "l=ho_fo_pattern p" and r: "r=ho_fo_pattern q"
    and wp: "ho_fo_wellformed F arity p" and wq: "ho_fo_wellformed F arity q"
    and vars: "ho_fo_variables q\<subseteq>ho_fo_variables p" and pq: "(p,q)\<in>P"
    using coverage[OF member head_l ho_fo_node_parts(1)[OF node]] by blast
  have t: "t=ho_fo_instance s p" and u: "u=ho_fo_instance s q"
    using li ri by (simp_all add: l r ho_fo_pattern_instantiate)
  have variables_safe: "\<forall>n\<in>ho_fo_variables p. ho_projection_safe F arity (s n)"
    using safe ho_projection_safe_instance[OF wp, of s] t by simp
  have safe_u: "ho_projection_safe F arity u"
    using variables_safe vars ho_projection_safe_instance[OF wq, of s] u by blast
  have edge: "rel (ho_context_projection F arity ce t) (ho_context_projection F arity ce u)"
    using instances[OF pq, of "\<lambda>n. ho_context_projection F arity ce (s n)"]
      ho_context_projection_instance[OF wp, of ce s]
      ho_context_projection_instance[OF wq, of ce s]
    by (simp add: t u)
  show ?thesis using safe_u edge by (auto intro: tranclp.r_into_trancl)
qed

end
end
