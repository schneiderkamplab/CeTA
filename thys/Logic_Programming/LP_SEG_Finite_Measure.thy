theory LP_SEG_Finite_Measure
  imports LP_Symbolic_Evaluation
begin

lemma lp_seg_ieval_injective:
  "lp_ieval s LPIVar = lp_ieval t LPIVar \<Longrightarrow> s=t"
proof (induct s arbitrary: t)
  case (Var x) then show ?case by (cases t) auto
next
  case (Fun f ss)
  obtain g ts where t: "t=Fun g ts" using Fun.prems by (cases t) auto
  have fg: "f=g" and maps: "map (\<lambda>s. lp_ieval s LPIVar) ss = map (\<lambda>t. lp_ieval t LPIVar) ts"
    using Fun.prems by (simp_all add: t)
  have len: "length ss=length ts" using arg_cong[OF maps, of length] by simp
  have "ss=ts"
  proof (rule nth_equalityI[OF len])
    fix i assume i: "i<length ss"
    have eq: "lp_ieval (ss!i) LPIVar=lp_ieval (ts!i) LPIVar"
      using arg_cong[OF maps, of "\<lambda>xs. xs!i"] i len by simp
    show "ss!i=ts!i" using Fun.hyps nth_mem[OF i] eq by auto
  qed
  then show ?case by (simp add: t fg)
qed

definition lp_seg_measure where
  "lp_seg_measure f G \<rho> t = (lp_ieval t LPIVar = LPIFun f (map \<rho> G))"

lemma lp_seg_measure_exists:
  assumes "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
  shows "\<exists>t. lp_seg_measure f G \<rho> t"
proof -
  obtain ts where ts: "map (\<lambda>t. lp_ieval t LPIVar) ts=map \<rho> G"
    using lp_seg_finite_list[of "map \<rho> G"] lp_seg_ground_finite assms by auto
  show ?thesis by (rule exI[of _ "Fun f ts"]) (simp add: lp_seg_measure_def ts)
qed

lemma lp_seg_measure_unique:
  "lp_seg_measure f G \<rho> s \<Longrightarrow> lp_seg_measure f G \<rho> t \<Longrightarrow> s=t"
  unfolding lp_seg_measure_def by (rule lp_seg_ieval_injective) simp

lemma lp_seg_finite_valuation:
  fixes \<rho> :: "'a \<Rightarrow> ('f,'v) lp_iterm"
  assumes "\<forall>x\<in>V. lp_seg_ground (\<rho> x)"
  shows "\<exists>\<sigma>. \<forall>x\<in>V. lp_ieval (\<sigma> x) LPIVar=\<rho> x"
proof -
  have "\<forall>x\<in>V. \<exists>t :: ('f,'v) term. lp_ieval t LPIVar=\<rho> x"
    using assms lp_seg_ground_finite by blast
  then show ?thesis by (rule bchoice)
qed

text \<open>A graph edge becomes an ordinary finite rewrite step only when all
  data it carries has a finite ground interpretation. This lemma is deliberately
  separate from source-graph coverage and the source-to-edge simulation.\<close>

lemma lp_seg_rewrite_measure:
  fixes \<rho> \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes measured: "lp_seg_measure f G \<rho> t"
    and rule: "(Fun f inputs,Fun g outputs)\<in>R"
    and input: "map (\<lambda>s. lp_ieval s \<eta>) inputs=map \<rho> G"
    and out_terms: "map (\<lambda>s. lp_ieval s \<eta>) outputs=map \<nu> H"
    and finite: "\<forall>x\<in>\<Union>(vars_term ` set inputs). lp_seg_ground (\<eta> x)"
    and vars: "\<Union>(vars_term ` set outputs) \<subseteq> \<Union>(vars_term ` set inputs)"
  shows "\<exists>u. (t,u)\<in>rstep R \<and> lp_seg_measure g H \<nu> u"
proof -
  obtain \<sigma> where sigma: "\<forall>x\<in>\<Union>(vars_term ` set inputs). lp_ieval (\<sigma> x) LPIVar=\<eta> x"
    using lp_seg_finite_valuation[OF finite] by blast
  have in_eval: "map (\<lambda>s. lp_ieval (s\<cdot>\<sigma>) LPIVar) inputs = map (\<lambda>s. lp_ieval s \<eta>) inputs"
    by (rule map_cong) (use sigma in \<open>auto simp: lp_ieval_finite_subst intro!: lp_ieval_cong\<close>)
  have out_eval: "map (\<lambda>s. lp_ieval (s\<cdot>\<sigma>) LPIVar) outputs = map (\<lambda>s. lp_ieval s \<eta>) outputs"
    by (rule map_cong) (use sigma vars in \<open>auto simp: lp_ieval_finite_subst intro!: lp_ieval_cong\<close>)
  have source: "t=Fun f inputs\<cdot>\<sigma>"
    by (rule lp_seg_ieval_injective) (use measured input in_eval in \<open>simp add: lp_seg_measure_def o_def\<close>)
  have step: "(Fun f inputs\<cdot>\<sigma>,Fun g outputs\<cdot>\<sigma>)\<in>rstep R"
    by (rule rstep.intros[OF rule, where C=Hole and \<sigma>=\<sigma>]) simp_all
  have target: "lp_seg_measure g H \<nu> (Fun g outputs\<cdot>\<sigma>)"
    using out_eval out_terms by (simp add: lp_seg_measure_def o_def)
  show ?thesis using step target source by blast
qed

end
