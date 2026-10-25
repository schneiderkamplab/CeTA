theory LP_Cut_Uniform_Free
  imports LP_Cut_Mixed_Free_Coverage LP_Cut_MGU_Context_Free
begin

lemma lpc_uniform_free_comparison:
  fixes a h :: "('f,string) term" and eta theta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes vars: "vars_term a \<subseteq> G\<union>F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G\<inter>vars_term a. s x=Var x"
    and theta: "\<forall>x\<in>G. theta x=eta x"
    and eq: "a\<cdot>s=h\<cdot>r"
  shows "\<exists>sigma :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a eta) sigma=lp_ieval h (\<lambda>x. lp_ieval (r x) theta)"
proof -
  obtain f where inj: "inj_on f F" and repr: "\<forall>x\<in>F. eta x=LPIVar (f x)"
    using lpc_free_knowledge_representation[OF free] by blast
  let ?sigma = "\<lambda>y. if y\<in>f ` F then lp_ieval (s (inv_into F f y)) theta else LPIVar y"
  have images: "lp_isubst (eta x) ?sigma=lp_ieval (s x) theta" if x: "x\<in>vars_term a" for x
  proof (cases "x\<in>F")
    case True
    then show ?thesis using repr inj by (simp add: inv_into_f_f)
  next
    case False
    have g: "x\<in>G" using vars x False by blast
    have gr: "lp_seg_ground (eta x)" using ground g by blast
    have sx: "s x=Var x" using same g x by blast
    have th: "theta x=eta x" using theta g by blast
    show ?thesis using gr by (simp add: sx th lp_seg_ground_subst)
  qed
  have "lp_isubst (lp_ieval a eta) ?sigma=lp_ieval (a\<cdot>s) theta"
    unfolding lp_ieval_subst lp_ieval_finite_subst
    by (rule lp_ieval_cong[OF images])
  also have "...=lp_ieval h (\<lambda>x. lp_ieval (r x) theta)"
    by (simp add: eq lp_ieval_finite_subst)
  finally show ?thesis by blast
qed

lemma lpc_uniform_free_block:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) gs h bs sigma rho"
    and vars: "vars_term a \<subseteq> G\<union>F"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge F eta"
    and same: "\<forall>x\<in>G\<inter>vars_term a. s x=Var x"
    and eq: "a\<cdot>s=h\<cdot>r"
    and occurs: "C\<subseteq>vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    and images: "\<forall>x\<in>C. \<exists>v. r x=Var v \<and> v\<notin>G"
    and distinct: "inj_on r C"
  shows "lpc_free_knowledge C rho"
proof -
  let ?theta = "\<lambda>x. if x\<in>G then eta x else LPIVar x"
  let ?nu = "\<lambda>x. lp_ieval (r x) ?theta"
  obtain tau :: "string \<Rightarrow> ('f,string) lp_iterm" where comparison:
    "lp_isubst (lp_ieval a eta) tau=lp_ieval h ?nu"
    using lpc_uniform_free_comparison[OF vars ground free same _ eq, where theta="?theta"]
    by auto
  have variable: "\<forall>x\<in>C. \<exists>v. ?nu x=LPIVar v" using images by auto
  have injective: "inj_on ?nu C"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>C" and y: "y\<in>C" and eq': "?nu x=?nu y"
    obtain u v where xv: "r x=Var u" "u\<notin>G" and yv: "r y=Var v" "v\<notin>G" using images x y by blast
    have "u=v" using eq' by (simp add: xv yv)
    then have "r x=r y" using xv yv by simp
    then show "x=y" by (rule inj_onD[OF distinct _ x y])
  qed
  have nu_free: "lpc_free_knowledge C ?nu" using variable injective by (simp add: lpc_free_knowledge_def)
  show ?thesis
    by (rule lpc_mgu_free_block_from_comparison[OF lpc_mgu_head_observation[OF mgu] comparison _ nu_free])
      (use occurs in auto)
qed

definition lpc_uniform_free_outputs where
  "lpc_uniform_free_outputs fuel k G F a h bs =
    (let h'=h\<cdot>(\<lambda>x. Var (lp_prefix k x));
      V=sorted_list_of_set (vars_term a \<union> vars_term h');
      W=remdups (vars_term_list h @ concat (map (\<lambda>g. concat (map vars_term_list (lp_cut_terms g))) bs)) in
      if vars_term a \<subseteq> set G\<union>set F then
      (case lp_cut_normalize fuel [(h',a)] (map (\<lambda>x. LPCAtom (Var x)) V) of
        Some (Some gs) \<Rightarrow>
          (let s=lpc_mgu_substitution V (map lpc_free_goal_term gs);
               r=\<lambda>x. s (lp_prefix k x);
               C=filter (\<lambda>x. case r x of Var v \<Rightarrow> v\<notin>set G | _ \<Rightarrow> False) W in
           if (\<forall>x\<in>set G\<inter>vars_term a. s x=Var x) \<and> a\<cdot>s=h'\<cdot>s \<and> distinct (map r C)
           then C else [])
      | _ \<Rightarrow> []) else [])"

lemma lpc_uniform_free_outputs_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a eta) gs h bs sigma rho"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
  shows "lpc_free_knowledge (set (lpc_uniform_free_outputs fuel k G F a h bs)) rho"
proof -
  let ?h="h\<cdot>(\<lambda>x. Var (lp_prefix k x))"
  let ?V="sorted_list_of_set (vars_term a \<union> vars_term ?h)"
  let ?W="remdups (vars_term_list h @ concat (map (\<lambda>g. concat (map vars_term_list (lp_cut_terms g))) bs))"
  let ?N="lp_cut_normalize fuel [(?h,a)] (map (\<lambda>x. LPCAtom (Var x)) ?V)"
  have empty: "lpc_free_knowledge {} rho" by (simp add: lpc_free_knowledge_def)
  show ?thesis
  proof (cases "vars_term a \<subseteq> set G\<union>set F")
    case False then show ?thesis by (simp add: lpc_uniform_free_outputs_def empty)
  next
    case True
    note vars=True
    show ?thesis
    proof (cases ?N)
      case None then show ?thesis by (simp only: lpc_uniform_free_outputs_def Let_def vars if_True option.simps list.set empty)
    next
      case (Some opt)
      note outer=Some
      show ?thesis
      proof (cases opt)
        case None then show ?thesis by (simp only: lpc_uniform_free_outputs_def Let_def vars if_True outer option.simps list.set empty)
      next
        case (Some gs')
        let ?s="lpc_mgu_substitution ?V (map lpc_free_goal_term gs')"
        let ?r="\<lambda>x. ?s (lp_prefix k x)"
        let ?C="filter (\<lambda>x. case ?r x of Var v \<Rightarrow> v\<notin>set G | _ \<Rightarrow> False) ?W"
        show ?thesis
        proof (cases "(\<forall>x\<in>set G\<inter>vars_term a. ?s x=Var x) \<and> a\<cdot>?s=?h\<cdot>?s \<and> distinct (map ?r ?C)")
          case False then show ?thesis by (simp only: lpc_uniform_free_outputs_def Let_def vars if_True outer Some option.simps if_False list.set empty)
        next
          case True
          have same: "\<forall>x\<in>set G\<inter>vars_term a. ?s x=Var x" using True by blast
          have eq: "a\<cdot>?s=h\<cdot>?r" using True
            by (simp only: subst_subst_compose[symmetric] subst_compose_def Term.eval_term.simps; blast)
          have occurs: "set ?C \<subseteq> vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
            by auto
          have images: "\<forall>x\<in>set ?C. \<exists>v. ?r x=Var v \<and> v\<notin>set G"
            by (auto split: term.splits)
          have inj: "inj_on ?r (set ?C)" using True by (simp add: distinct_map)
          have known: "lpc_free_knowledge (set ?C) rho"
            by (rule lpc_uniform_free_block[OF mgu vars ground free same eq occurs images inj])
          show ?thesis using known by (simp only: lpc_uniform_free_outputs_def Let_def vars if_True outer Some option.simps if_P[OF True])
        qed
      qed
    qed
  qed
qed

end
