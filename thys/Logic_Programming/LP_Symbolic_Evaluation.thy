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

lemma lp_seg_isubst_comp:
  "lp_isubst (lp_isubst t \<sigma>) \<tau> = lp_isubst t (\<lambda>x. lp_isubst (\<sigma> x) \<tau>)"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl_strong split: lp_iterm.splits)

lemma lp_seg_ground_subst:
  "lp_seg_ground t \<Longrightarrow> lp_isubst t \<sigma> = t"
  by (induct rule: lp_seg_ground.induct)
    (auto simp: list_all_iff intro!: map_idI)

lemma lp_seg_nonunifiable_subst:
  fixes s t :: "('f,'v) lp_iterm" and \<sigma> :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes "lp_seg_nonunifiable s t"
  shows "lp_seg_nonunifiable (lp_isubst s \<sigma>) (lp_isubst t \<sigma>)"
  using assms unfolding lp_seg_nonunifiable_def
  by (simp only: lp_seg_isubst_comp) blast

lemma lp_seg_knowledge_subst:
  fixes \<rho> :: "'a \<Rightarrow> ('f,'v) lp_iterm" and \<sigma> :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes "lp_seg_knowledge G U \<rho>"
  shows "lp_seg_knowledge G U (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
  using assms unfolding lp_seg_knowledge_def
  by (auto simp: lp_seg_ground_subst lp_ieval_subst[symmetric]
    intro: lp_seg_nonunifiable_subst)

text \<open>Sequential composition: terminating prefixes can be followed by a
  continuation whose source knowledge is stable under answer substitutions.
  This also covers infinite runtime substitutions; it does not assume an MGU
  with an occurs check.\<close>

lemma lp_seg_append_sn_invariant:
  fixes P :: "('f,string) lp_clause list"
    and prefix :: "('f,string) lp_iatom list"
    and rest :: "('f,string) lp_atom list"
    and K :: "(string \<Rightarrow> ('f,string) lp_iterm) \<Rightarrow> bool"
  assumes sn: "SN_on (lp_ild P) {prefix}"
    and suffix: "\<And>\<rho>. K \<rho> \<Longrightarrow>
      SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    and stable: "\<And>\<rho> \<sigma>. K \<rho> \<Longrightarrow> K (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    and initial: "K \<rho>"
  shows "SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
proof -
  have all: "\<forall>\<rho>. K \<rho> \<longrightarrow>
    SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix ps :: "('f,string) lp_iatom list"
    assume ih: "\<And>qs. (ps,qs)\<in>lp_ild P \<Longrightarrow>
      \<forall>\<rho>. K \<rho> \<longrightarrow>
        SN_on (lp_ild P) {qs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    show "\<forall>\<rho>. K \<rho> \<longrightarrow>
      SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    proof (intro allI impI)
      fix \<rho> assume k: "K \<rho>"
      show "SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
      proof (cases ps)
        case Nil then show ?thesis using suffix[OF k] by simp
      next
        case (Cons a tail)
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix hs assume step: "(ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,hs)\<in>lp_ild P"
          obtain c \<sigma> \<nu> where c: "c<length P"
            and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
            and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
              map (\<lambda>b. lp_iatom_subst b \<sigma>) (tail @ map (\<lambda>a. lp_atom_eval a \<rho>) rest)"
            using lp_ild_cons_cases step unfolding Cons append_Cons by blast
          let ?qs = "map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
            map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
          have transition: "(ps,?qs)\<in>lp_ild P"
            unfolding Cons by (rule lp_ild.resolve[OF c eq])
          have post: "K (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
            by (rule stable[OF k])
          have "SN_on (lp_ild P) {?qs @ map (\<lambda>a. lp_atom_eval a
            (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)) rest}"
            using ih[OF transition] post by blast
          then show "SN_on (lp_ild P) {hs}" by (simp add: hs o_def)
        qed
      qed
    qed
  qed
  show ?thesis using all initial by blast
qed

lemma lp_seg_fixed_ground_stable:
  assumes ground: "\<forall>x\<in>set G. lp_seg_ground (\<rho> x)"
    and fixed: "map \<rho> G = vals"
  shows "(\<forall>x\<in>set G. lp_seg_ground (lp_isubst (\<rho> x) \<sigma>)) \<and>
    map (\<lambda>x. lp_isubst (\<rho> x) \<sigma>) G = vals"
  using ground fixed by (auto simp: lp_seg_ground_subst intro!: map_cong)

lemma lp_seg_append_sn:
  fixes P :: "('f,string) lp_clause list"
    and prefix :: "('f,string) lp_iatom list"
    and rest :: "('f,string) lp_atom list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes sn: "SN_on (lp_ild P) {prefix}"
    and suffix: "\<And>\<rho> :: string \<Rightarrow> ('f,string) lp_iterm.
      lp_seg_knowledge G U \<rho> \<Longrightarrow>
      SN_on (lp_ild P) {map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    and knowledge: "lp_seg_knowledge G U \<rho>"
  shows "SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
proof -
  have all: "\<forall>\<rho>. lp_seg_knowledge G U \<rho> \<longrightarrow>
    SN_on (lp_ild P) {prefix @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
  proof (rule SN_on_induct[OF sn singletonI])
    fix ps :: "('f,string) lp_iatom list"
    assume ih: "\<And>qs. (ps,qs)\<in>lp_ild P \<Longrightarrow>
      \<forall>\<rho>. lp_seg_knowledge G U \<rho> \<longrightarrow>
        SN_on (lp_ild P) {qs @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    show "\<forall>\<rho>. lp_seg_knowledge G U \<rho> \<longrightarrow>
      SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
    proof (intro allI impI)
      fix \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
      assume k: "lp_seg_knowledge G U \<rho>"
      show "SN_on (lp_ild P) {ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest}"
      proof (cases ps)
        case Nil then show ?thesis using suffix[OF k] by simp
      next
        case (Cons a tail)
        show ?thesis
        proof (rule step_reflects_SN_on)
          fix hs assume step: "(ps @ map (\<lambda>a. lp_atom_eval a \<rho>) rest,hs)\<in>lp_ild P"
          obtain c \<sigma> \<nu> where c: "c<length P"
            and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
            and hs: "hs=map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
              map (\<lambda>b. lp_iatom_subst b \<sigma>) (tail @ map (\<lambda>a. lp_atom_eval a \<rho>) rest)"
            using lp_ild_cons_cases step unfolding Cons append_Cons by blast
          let ?qs = "map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
            map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
          have transition: "(ps,?qs)\<in>lp_ild P"
            unfolding Cons by (rule lp_ild.resolve[OF c eq])
          have post: "lp_seg_knowledge G U (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
            by (rule lp_seg_knowledge_subst[OF k])
          have "SN_on (lp_ild P) {?qs @ map (\<lambda>a. lp_atom_eval a
            (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)) rest}"
            using ih[OF transition] post by blast
          then show "SN_on (lp_ild P) {hs}" by (simp add: hs o_def)
        qed
      qed
    qed
  qed
  show ?thesis using all knowledge by blast
qed

definition lp_seg_split_rename where
  "lp_seg_split_rename k G x = Var (if x\<in>G then x else lp_prefix k x)"

definition lp_seg_split_env where
  "lp_seg_split_env k \<rho> y = (if length y<k then \<rho> y else \<rho> (drop k y))"

lemma lp_seg_split_eval:
  assumes "\<forall>x\<in>vars_term t. length x<k"
  shows "lp_ieval (t\<cdot>lp_seg_split_rename k G) (lp_seg_split_env k \<rho>) = lp_ieval t \<rho>"
  unfolding lp_ieval_finite_subst
  by (rule lp_ieval_cong) (use assms in \<open>auto simp: lp_seg_split_rename_def lp_seg_split_env_def lp_prefix_def\<close>)

lemma lp_seg_split_atom:
  assumes "\<forall>t\<in>set (snd a). \<forall>x\<in>vars_term t. length x<k"
  shows "lp_atom_eval (lp_atom_subst a (lp_seg_split_rename k G)) (lp_seg_split_env k \<rho>) = lp_atom_eval a \<rho>"
  using assms unfolding lp_atom_subst_def lp_atom_eval_def
  by (auto simp: o_def intro!: map_cong lp_seg_split_eval)

lemma lp_seg_split_concretization:
  assumes goals: "lp_short_goals k rest"
    and ground: "\<forall>x\<in>G. length x<k"
    and constraints: "\<forall>(s,t)\<in>U. \<forall>x\<in>vars_term s \<union> vars_term t. length x<k"
    and knowledge: "lp_seg_knowledge G U \<rho>"
  shows "map (\<lambda>a. lp_atom_eval a \<rho>) rest \<in>
    lp_seg_concretizations (map (\<lambda>a. lp_atom_subst a (lp_seg_split_rename k G)) rest)
      G ((\<lambda>(s,t). (s\<cdot>lp_seg_split_rename k G,t\<cdot>lp_seg_split_rename k G)) ` U)"
proof -
  have preserved: "\<And>s t. (s,t)\<in>U \<Longrightarrow>
    lp_seg_nonunifiable (lp_ieval (s\<cdot>lp_seg_split_rename k G) (lp_seg_split_env k \<rho>))
      (lp_ieval (t\<cdot>lp_seg_split_rename k G) (lp_seg_split_env k \<rho>))"
  proof -
    fix s t assume st: "(s,t)\<in>U"
    have bs: "\<forall>x\<in>vars_term s. length x<k" and bt: "\<forall>x\<in>vars_term t. length x<k"
      using constraints st by auto
    have original: "lp_seg_nonunifiable (lp_ieval s \<rho>) (lp_ieval t \<rho>)"
      using knowledge st unfolding lp_seg_knowledge_def by auto
    show "lp_seg_nonunifiable (lp_ieval (s\<cdot>lp_seg_split_rename k G) (lp_seg_split_env k \<rho>))
      (lp_ieval (t\<cdot>lp_seg_split_rename k G) (lp_seg_split_env k \<rho>))"
      using original by (simp only: lp_seg_split_eval[OF bs] lp_seg_split_eval[OF bt])
  qed
  have k: "lp_seg_knowledge G
    ((\<lambda>(s,t). (s\<cdot>lp_seg_split_rename k G,t\<cdot>lp_seg_split_rename k G)) ` U)
    (lp_seg_split_env k \<rho>)"
    using knowledge ground preserved unfolding lp_seg_knowledge_def
    by (auto simp: lp_seg_split_env_def)
  have eq: "map (\<lambda>a. lp_atom_eval a (lp_seg_split_env k \<rho>))
    (map (\<lambda>a. lp_atom_subst a (lp_seg_split_rename k G)) rest) =
    map (\<lambda>a. lp_atom_eval a \<rho>) rest"
    using goals unfolding lp_short_goals_def
    by (auto simp: o_def list_all_iff intro!: map_cong lp_seg_split_atom)
  show ?thesis unfolding lp_seg_concretizations_def mem_Collect_eq
    by (rule exI[of _ "lp_seg_split_env k \<rho>"]) (use k eq in auto)
qed

theorem lp_seg_split_sound:
  fixes P :: "('f,string) lp_clause list"
    and \<rho> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes goals: "lp_short_goals k rest"
    and ground: "\<forall>x\<in>G. length x<k"
    and constraints: "\<forall>(s,t)\<in>U. \<forall>x\<in>vars_term s \<union> vars_term t. length x<k"
    and knowledge: "lp_seg_knowledge G U \<rho>"
    and first: "SN_on (lp_ild P) {[lp_atom_eval a \<rho>]}"
    and second: "\<And>gs :: ('f,string) lp_iatom list.
      gs \<in> lp_seg_concretizations
        (map (\<lambda>a. lp_atom_subst a (lp_seg_split_rename k G)) rest)
        G ((\<lambda>(s,t). (s\<cdot>lp_seg_split_rename k G,t\<cdot>lp_seg_split_rename k G)) ` U)
      \<Longrightarrow> SN_on (lp_ild P) {gs}"
  shows "SN_on (lp_ild P) {map (\<lambda>b. lp_atom_eval b \<rho>) (a#rest)}"
proof -
  have "SN_on (lp_ild P) {[lp_atom_eval a \<rho>] @ map (\<lambda>b. lp_atom_eval b \<rho>) rest}"
    by (rule lp_seg_append_sn[OF first _ knowledge])
      (rule second, rule lp_seg_split_concretization[OF goals ground constraints], assumption)
  then show ?thesis by simp
qed

lemma lp_seg_finite_list:
  assumes "\<forall>u\<in>set ts. \<exists>t :: ('f,'v) term. ground t \<and> lp_ieval t LPIVar=u"
  shows "\<exists>us :: ('f,'v) term list. list_all ground us \<and> map (\<lambda>t. lp_ieval t LPIVar) us=ts"
  using assms
proof (induct ts)
  case Nil then show ?case by auto
next
  case (Cons t ts)
  obtain u where u: "ground u" "lp_ieval u LPIVar=t" using Cons.prems by auto
  obtain us where us: "list_all ground us" "map (\<lambda>t. lp_ieval t LPIVar) us=ts"
    using Cons.hyps Cons.prems by auto
  show ?case by (rule exI[of _ "u#us"]) (use u us in simp)
qed

lemma lp_seg_ground_finite:
  "lp_seg_ground u \<Longrightarrow> \<exists>t :: ('f,'v) term. ground t \<and> lp_ieval t LPIVar=u"
proof (induct rule: lp_seg_ground.induct)
  case (node ts f)
  obtain us where us: "list_all ground us" "map (\<lambda>t. lp_ieval t LPIVar) us=ts"
    using lp_seg_finite_list node.hyps by (auto simp: list_all_iff)
  show ?case by (rule exI[of _ "Fun f us"]) (use us in \<open>auto simp: list_all_iff\<close>)
qed

text \<open>The finite-data bridge is needed before applying ordinary TRS
  termination to a cyclic graph. Non-ground/rational variables must not be
  smuggled into finite-term termination measures.\<close>

end
