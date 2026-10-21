theory LP_Symbolic_Evaluation
  imports LP_Source_Tree
begin

text \<open>Pure-LP symbolic evaluation foundations following PPDP 2012,
  Definitions 7 and 11. Unlike that paper's occurs-check semantics, valuations
  here may be infinite runtime trees. Ground knowledge explicitly means finite
  ground data. Instance edges express inclusion, not termination; cyclic graphs
  require a separate simulation and a certified termination obligation.\<close>

inductive lp_seg_ground :: "('f,'v) lp_iterm \<Rightarrow> bool" where
  node: "list_all lp_seg_ground ts \<Longrightarrow> lp_seg_ground (LPIFun f ts)"

lemma lp_seg_ground_fun[simp]:
  "lp_seg_ground (LPIFun f ts) = list_all lp_seg_ground ts"
  by (auto intro: lp_seg_ground.intros elim: lp_seg_ground.cases)

lemma lp_seg_ground_eval:
  "lp_seg_ground (lp_ieval t \<rho>) = (\<forall>x\<in>vars_term t. lp_seg_ground (\<rho> x))"
  by (induct t) (auto simp: list_all_iff)

definition lp_seg_nonunifiable :: "('f,'v) lp_iterm \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> bool" where
  "lp_seg_nonunifiable s t =
    (\<not>(\<exists>\<sigma> :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_isubst s \<sigma> = lp_isubst t \<sigma>))"

definition lp_seg_knowledge where
  "lp_seg_knowledge G U \<rho> =
    ((\<forall>x\<in>G. lp_seg_ground (\<rho> x)) \<and>
     (\<forall>(s,t)\<in>U. lp_seg_nonunifiable (lp_ieval s \<rho>) (lp_ieval t \<rho>)))"

definition lp_seg_concretizations where
  "lp_seg_concretizations gs G U =
    {map (\<lambda>a. lp_atom_eval a \<rho>) gs |\<rho>. lp_seg_knowledge G U \<rho>}"

lemma lp_seg_instance_knowledge:
  assumes ground: "G = (\<Union>x\<in>G'. vars_term (\<mu> x))"
    and constraints: "(\<lambda>(s,t). (s\<cdot>\<mu>,t\<cdot>\<mu>)) ` U' \<subseteq> U"
    and current: "lp_seg_knowledge G U \<rho>"
  shows "lp_seg_knowledge G' U' (\<lambda>x. lp_ieval (\<mu> x) \<rho>)"
proof -
  have g: "\<forall>x\<in>G'. lp_seg_ground (lp_ieval (\<mu> x) \<rho>)"
    using ground current by (auto simp: lp_seg_knowledge_def lp_seg_ground_eval)
  have u: "\<And>s t. (s,t)\<in>U' \<Longrightarrow>
    lp_seg_nonunifiable (lp_ieval s (\<lambda>x. lp_ieval (\<mu> x) \<rho>))
      (lp_ieval t (\<lambda>x. lp_ieval (\<mu> x) \<rho>))"
  proof -
    fix s t assume st: "(s,t)\<in>U'"
    have "(s\<cdot>\<mu>,t\<cdot>\<mu>)\<in>U"
      by (rule subsetD[OF constraints]) (use st in auto)
    then show "lp_seg_nonunifiable (lp_ieval s (\<lambda>x. lp_ieval (\<mu> x) \<rho>))
      (lp_ieval t (\<lambda>x. lp_ieval (\<mu> x) \<rho>))"
      using current unfolding lp_seg_knowledge_def
      by (auto simp: lp_ieval_finite_subst)
  qed
  show ?thesis using g u unfolding lp_seg_knowledge_def by auto
qed

theorem lp_seg_instance_sound:
  assumes goals: "gs = map (\<lambda>a. lp_atom_subst a \<mu>) gs'"
    and ground: "G = (\<Union>x\<in>G'. vars_term (\<mu> x))"
    and constraints: "(\<lambda>(s,t). (s\<cdot>\<mu>,t\<cdot>\<mu>)) ` U' \<subseteq> U"
  shows "lp_seg_concretizations gs G U \<subseteq> lp_seg_concretizations gs' G' U'"
proof
  fix concrete assume "concrete\<in>lp_seg_concretizations gs G U"
  then obtain \<rho> where concrete: "concrete=map (\<lambda>a. lp_atom_eval a \<rho>) gs"
    and knowledge: "lp_seg_knowledge G U \<rho>"
    unfolding lp_seg_concretizations_def by blast
  have target: "lp_seg_knowledge G' U' (\<lambda>x. lp_ieval (\<mu> x) \<rho>)"
    by (rule lp_seg_instance_knowledge[OF ground constraints knowledge])
  have "concrete=map (\<lambda>a. lp_atom_eval a (\<lambda>x. lp_ieval (\<mu> x) \<rho>)) gs'"
    by (simp add: concrete goals lp_atom_eval_finite_subst o_def)
  then show "concrete\<in>lp_seg_concretizations gs' G' U'"
    using target unfolding lp_seg_concretizations_def by blast
qed

end
