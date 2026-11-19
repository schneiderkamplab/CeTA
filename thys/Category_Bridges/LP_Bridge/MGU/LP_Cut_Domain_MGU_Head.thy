theory LP_Cut_Domain_MGU_Head
  imports LP_Cut_Domain_MGU_Properties
begin

text \<open>Free blocks derived from clause-head positions need one common
comparison substitution. Its values are either existing domain values or
variables, preserving the domain as well as pairwise variable separation.\<close>

context cut_runtime_domain
begin

lemma mgu_free_block_from_comparison:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_resolve a gs h bs \<sigma> \<rho>"
    and comparison: "lp_isubst a \<tau> = lp_ieval h \<nu>"
    and body: "F \<subseteq> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    and free: "lpc_free_knowledge F \<nu>"
    and domains: "\<forall>x. D (\<tau> x)" "\<forall>x. D (\<nu> x)"
  shows "lpc_free_knowledge F \<rho>"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm" where factor:
    "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using mgu_body_factor[OF mgu comparison domains] by blast
  have equation: "\<And>x. x\<in>F \<Longrightarrow> lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using factor body by blast
  have variables: "\<forall>x\<in>F. \<exists>y. \<rho> x=LPIVar y"
  proof (intro ballI)
    fix x assume x: "x\<in>F"
    obtain y where "\<nu> x=LPIVar y"
      using free x by (auto simp: lpc_free_knowledge_def)
    then have "lp_isubst (\<rho> x) \<delta> = LPIVar y"
      using equation[OF x] by simp
    then show "\<exists>y. \<rho> x=LPIVar y"
      by (rule lpc_isubst_variable_reflect)
  qed
  have injective: "inj_on \<rho> F"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>F" and y: "y\<in>F" and eq: "\<rho> x=\<rho> y"
    have "\<nu> x=\<nu> y" using equation[OF x] equation[OF y] eq by simp
    then show "x=y" using free x y by (auto simp: lpc_free_knowledge_def inj_on_def)
  qed
  show ?thesis using variables injective by (simp add: lpc_free_knowledge_def)
qed

theorem mgu_independent_head_knowledge:
  fixes ats :: "('f lp_cut_symbol,string) lp_iterm list"
    and hs :: "('f lp_cut_symbol,string) term list"
    and r :: "string \<Rightarrow> string"
  assumes mgu: "mgu_resolve (LPIFun f ats) gs (Fun f hs) bs \<sigma> \<rho>"
    and injective: "inj_on r H"
    and positions: "\<And>i. i<length hs \<Longrightarrow>
      (\<exists>x\<in>H. hs!i=Var x \<and> ats!i=LPIVar (r x)) \<or>
      (vars_term (hs!i) \<inter> H = {} \<and>
       (lp_seg_ground (ats!i) \<or> (\<exists>v. ats!i=LPIVar v \<and> v\<notin>r ` H)))"
  defines "Vbody \<equiv> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  shows "lpc_free_knowledge ((H \<inter> Vbody) \<union> lpc_body_only_variables (Fun f hs) bs) \<rho>"
proof -
  let ?B = "lpc_body_only_variables (Fun f hs) bs"
  let ?F = "(H \<inter> Vbody) \<union> ?B"
  let ?tau = "\<lambda>v. if v\<in>r ` H then LPIVar (inv_into H r v) else \<sigma> v"
  let ?nu = "\<lambda>x. if x\<in>H\<union>?B then LPIVar x else \<rho> x"
  have unifier: "lp_isubst (LPIFun f ats) \<sigma> = lp_ieval (Fun f hs) \<rho>"
    using mgu by (simp add: mgu_resolve_def)
  have absent: "?B \<inter> vars_term (Fun f hs) = {}"
    by (auto simp: lpc_body_only_variables_def)
  have comparison: "lp_isubst (LPIFun f ats) ?tau = lp_ieval (Fun f hs) ?nu"
    by (rule lpc_independent_head_comparison[OF unifier injective absent positions])
  have body: "?F \<subseteq> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    by (auto simp: Vbody_def lpc_body_only_variables_def)
  have free: "lpc_free_knowledge ?F ?nu"
    by (auto simp: lpc_free_knowledge_def inj_on_def)
  show ?thesis by (rule mgu_free_block_from_comparison[OF mgu comparison body free])
    (use mgu in \<open>auto simp: mgu_resolve_def intro: variables\<close>)
qed

theorem checked_head_links_knowledge:
  fixes ts hs :: "('f lp_cut_symbol,string) term list"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_resolve (lp_ieval (Fun f ts) \<eta>) gs (Fun f hs) bs \<sigma> \<rho>"
    and checked: "lpc_check_head_links F G ts hs links"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
  shows "lpc_free_knowledge
    ((set (map fst links) \<inter> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t))
      \<union> lpc_body_only_variables (Fun f hs) bs) \<rho>"
proof -
  let ?H = "set (map fst links)"
  let ?v = "lpc_head_link_value links"
  obtain r where inj: "inj_on r (set F)"
    and valuation: "\<forall>x\<in>set F. \<eta> x=LPIVar (r x)"
    using lpc_free_knowledge_representation[OF free] by blast
  have len: "length ts=length hs" and subset: "?v ` ?H \<subseteq> set F"
    and vi: "inj_on ?v ?H"
    using checked by (auto simp: lpc_check_head_links_def Let_def)
  have ri: "inj_on (r \<circ> ?v) ?H"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>?H" and y: "y\<in>?H"
      and eq: "(r \<circ> ?v) x = (r \<circ> ?v) y"
    have vx: "?v x\<in>set F" and vy: "?v y\<in>set F" using subset x y by blast+
    have "?v x=?v y" by (rule inj_onD[OF inj _ vx vy]) (use eq in simp)
    then show "x=y" by (rule inj_onD[OF vi _ x y])
  qed
  have positions: "\<And>i. i<length hs \<Longrightarrow>
      (\<exists>x\<in>?H. hs!i=Var x \<and> (map (\<lambda>t. lp_ieval t \<eta>) ts)!i=LPIVar ((r \<circ> ?v) x)) \<or>
      (vars_term (hs!i) \<inter> ?H = {} \<and>
       (lp_seg_ground ((map (\<lambda>t. lp_ieval t \<eta>) ts)!i) \<or>
        (\<exists>w. (map (\<lambda>t. lp_ieval t \<eta>) ts)!i=LPIVar w \<and> w\<notin>(r \<circ> ?v) ` ?H)))"
  proof -
    fix i assume ih: "i<length hs"
    then have it: "i<length ts" using len by simp
    have at:
      "(case hs!i of Var x \<Rightarrow> x\<in>?H \<and> ts!i=Var (?v x) | _ \<Rightarrow> False) \<or>
       (vars_term (hs!i) \<inter> ?H = {} \<and>
        (vars_term (ts!i) \<subseteq> set G \<or>
         (case ts!i of Var x \<Rightarrow> x\<in>set F \<and> x\<notin>?v ` ?H | _ \<Rightarrow> False)))"
      using checked ih
      by (simp only: lpc_check_head_links_def Let_def list_all_iff set_upt
          atLeastLessThan_iff zero_le; blast)
    have cases:
      "(\<exists>x\<in>?H. hs!i=Var x \<and> ts!i=Var (?v x)) \<or>
       (vars_term (hs!i) \<inter> ?H = {} \<and>
        (vars_term (ts!i) \<subseteq> set G \<or> (\<exists>x\<in>set F. ts!i=Var x \<and> x\<notin>?v ` ?H)))"
      using at by (auto split: term.splits)
    show "(\<exists>x\<in>?H. hs!i=Var x \<and> (map (\<lambda>t. lp_ieval t \<eta>) ts)!i=LPIVar ((r \<circ> ?v) x)) \<or>
      (vars_term (hs!i) \<inter> ?H = {} \<and>
       (lp_seg_ground ((map (\<lambda>t. lp_ieval t \<eta>) ts)!i) \<or>
        (\<exists>w. (map (\<lambda>t. lp_ieval t \<eta>) ts)!i=LPIVar w \<and> w\<notin>(r \<circ> ?v) ` ?H)))"
    proof (cases "\<exists>x\<in>?H. hs!i=Var x \<and> ts!i=Var (?v x)")
      case True
      then obtain x where x: "x\<in>?H" "hs!i=Var x" "ts!i=Var (?v x)" by blast
      have "?v x\<in>set F" using subset x(1) by blast
      then show ?thesis using valuation x it by auto
    next
      case False
      then have head: "vars_term (hs!i) \<inter> ?H = {}"
        and kind: "vars_term (ts!i) \<subseteq> set G \<or> (\<exists>x\<in>set F. ts!i=Var x \<and> x\<notin>?v ` ?H)"
        using cases by blast+
      have tail: "lp_seg_ground (lp_ieval (ts!i) \<eta>) \<or>
          (\<exists>w. lp_ieval (ts!i) \<eta>=LPIVar w \<and> w\<notin>(r \<circ> ?v) ` ?H)"
      proof (cases "vars_term (ts!i) \<subseteq> set G")
        case True
        then have "lp_seg_ground (lp_ieval (ts!i) \<eta>)"
          using ground by (auto simp: lp_seg_ground_eval)
        then show ?thesis by simp
      next
        case False
        then obtain x where x: "x\<in>set F" "ts!i=Var x" "x\<notin>?v ` ?H" using kind by blast
        have outside: "r x\<notin>(r \<circ> ?v) ` ?H"
        proof
          assume "r x\<in>(r \<circ> ?v) ` ?H"
          then obtain y where y: "y\<in>?H" and eq: "r x=r (?v y)" by auto
          have vy: "?v y\<in>set F" using subset y by blast
          have "x=?v y" by (rule inj_onD[OF inj eq x(1) vy])
          then show False using x(3) y by blast
        qed
        have "lp_ieval (ts!i) \<eta>=LPIVar (r x)" using valuation x by simp
        then show ?thesis using outside by blast
      qed
      show ?thesis using head tail it by simp
    qed
  qed
  show ?thesis
    by (rule mgu_independent_head_knowledge[OF _ ri positions]) (use mgu in simp)
qed

theorem result_free_variables_sound:
  assumes mgu: "mgu_resolve (lp_ieval a \<eta>) gs h bs \<sigma> \<rho>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
  shows "lpc_free_knowledge (lpc_result_free_variables F G a h bs) \<rho>"
proof (cases a)
  case (Var x)
  then show ?thesis using mgu_body_only_knowledge[OF mgu]
    by (simp add: lpc_result_free_variables_def split: term.splits)
next
  case A: (Fun f ts)
  show ?thesis
  proof (cases h)
    case (Var x)
    then show ?thesis using A mgu_body_only_knowledge[OF mgu]
      by (simp add: lpc_result_free_variables_def)
  next
    case H: (Fun g hs)
    let ?links = "concat (map (lpc_head_link_candidate F) (zip ts hs))"
    show ?thesis
    proof (cases "f=g \<and> lpc_check_head_links F G ts hs ?links")
      case True
      have mg: "mgu_resolve (lp_ieval (Fun f ts) \<eta>) gs (Fun f hs) bs \<sigma> \<rho>"
        using mgu A H True by simp
      have chk: "lpc_check_head_links F G ts hs ?links" using True by simp
      have fact: "lpc_free_knowledge
        ((set (map fst ?links) \<inter> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t))
          \<union> lpc_body_only_variables (Fun f hs) bs) \<rho>"
        by (rule checked_head_links_knowledge[OF mg chk free ground])
      show ?thesis using fact A H True
        by (simp add: lpc_result_free_variables_def Let_def)
    next
      case False
      then show ?thesis using A H mgu_body_only_knowledge[OF mgu]
        by (simp add: lpc_result_free_variables_def Let_def; blast)
    qed
  qed
qed

lemma mgu_result_free_sound:
  assumes mgu: "mgu_resolve (lp_ieval a \<eta>) gs h bs \<sigma> \<rho>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
  shows "lpc_free_knowledge (set (lpc_mgu_result_free F G a h bs l))
    (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
proof -
  let ?F = "lpc_result_free_variables F G a h bs"
  have known: "lpc_free_knowledge ?F \<rho>"
    by (rule result_free_variables_sound[OF mgu free ground])
  have env: "\<And>x. lp_cut_resolution_env k l \<eta> \<sigma> \<rho> (lp_prefix l x) = \<rho> x"
    by (simp add: lp_cut_resolution_env_def lp_prefix_def)
  have source: "set (lpc_mgu_result_free F G a h bs l) = lp_prefix l ` ?F"
    by (simp add: lpc_mgu_result_free_def lpc_result_free_variables_finite)
  show ?thesis using known
    by (auto simp: source lpc_free_knowledge_def inj_on_def env)
qed

end
end
