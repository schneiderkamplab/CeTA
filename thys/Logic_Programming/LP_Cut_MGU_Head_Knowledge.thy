theory LP_Cut_MGU_Head_Knowledge
  imports LP_Cut_MGU_Coverage
begin

text \<open>A common comparison unifier proves a whole free-variable block,
including separation. Checking variables one at a time would not suffice.\<close>

lemma lpc_mgu_free_block_from_comparison:
  fixes a :: "('f,string) lp_iterm"
    and \<tau> \<nu> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a gs h bs \<sigma> \<rho>"
    and comparison: "lp_isubst a \<tau> = lp_ieval h \<nu>"
    and body: "F \<subseteq> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    and free: "lpc_free_knowledge F \<nu>"
  shows "lpc_free_knowledge F \<rho>"
proof -
  obtain \<delta> :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "\<forall>g\<in>set bs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (\<rho> x) \<delta> = \<nu> x"
    using lpc_mgu_body_factor[OF mgu comparison] by blast
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

lemma lpc_independent_head_comparison:
  fixes ats :: "('f,string) lp_iterm list"
    and hs :: "('f,string) term list"
    and r :: "string \<Rightarrow> string"
  assumes unifier: "lp_isubst (LPIFun f ats) \<sigma> = lp_ieval (Fun f hs) \<rho>"
    and injective: "inj_on r H"
    and absent: "B \<inter> vars_term (Fun f hs) = {}"
    and positions: "\<And>i. i<length hs \<Longrightarrow>
      (\<exists>x\<in>H. hs!i=Var x \<and> ats!i=LPIVar (r x)) \<or>
      (vars_term (hs!i) \<inter> H = {} \<and>
       (lp_seg_ground (ats!i) \<or> (\<exists>v. ats!i=LPIVar v \<and> v\<notin>r ` H)))"
  defines "\<tau> \<equiv> \<lambda>v. if v\<in>r ` H then LPIVar (inv_into H r v) else \<sigma> v"
    and "\<nu> \<equiv> \<lambda>x. if x\<in>H\<union>B then LPIVar x else \<rho> x"
  shows "lp_isubst (LPIFun f ats) \<tau> = lp_ieval (Fun f hs) \<nu>"
proof -
  have original: "map (\<lambda>t. lp_isubst t \<sigma>) ats = map (\<lambda>t. lp_ieval t \<rho>) hs"
    using unifier by simp
  have len: "length ats=length hs" using arg_cong[OF original, of length] by simp
  have maps: "map (\<lambda>t. lp_isubst t \<tau>) ats = map (\<lambda>t. lp_ieval t \<nu>) hs"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>t. lp_isubst t \<tau>) ats) = length (map (\<lambda>t. lp_ieval t \<nu>) hs)"
      using len by simp
    fix i assume bound: "i<length (map (\<lambda>t. lp_isubst t \<tau>) ats)"
    then have ih: "i<length hs" and ia: "i<length ats" using len by simp_all
    have old: "lp_isubst (ats!i) \<sigma> = lp_ieval (hs!i) \<rho>"
      using arg_cong[OF original, of "\<lambda>xs. xs!i"] ih ia by simp
    have eq: "lp_isubst (ats!i) \<tau> = lp_ieval (hs!i) \<nu>"
    proof (cases "\<exists>x\<in>H. hs!i=Var x \<and> ats!i=LPIVar (r x)")
      case True
      then obtain x where x: "x\<in>H" "hs!i=Var x" "ats!i=LPIVar (r x)" by blast
      have inverse: "inv_into H r (r x) = x" by (rule inv_into_f_f[OF injective x(1)])
      show ?thesis using x inverse by (simp add: \<tau>_def \<nu>_def)
    next
      case False
      then have head: "vars_term (hs!i) \<inter> H = {}"
        and call: "lp_seg_ground (ats!i) \<or> (\<exists>v. ats!i=LPIVar v \<and> v\<notin>r ` H)"
        using positions[OF ih] by blast+
      have body: "vars_term (hs!i) \<inter> B = {}" using absent nth_mem[OF ih]
        by auto
      have rhs: "lp_ieval (hs!i) \<nu> = lp_ieval (hs!i) \<rho>"
        by (rule lp_ieval_cong) (use head body in \<open>auto simp: \<nu>_def\<close>)
      have lhs: "lp_isubst (ats!i) \<tau> = lp_isubst (ats!i) \<sigma>"
        using call by (auto simp: \<tau>_def lp_seg_ground_subst)
      show ?thesis using lhs rhs old by simp
    qed
    show "map (\<lambda>t. lp_isubst t \<tau>) ats ! i = map (\<lambda>t. lp_ieval t \<nu>) hs ! i"
      using eq ih ia by simp
  qed
  show ?thesis using maps by simp
qed

theorem lpc_mgu_independent_head_knowledge:
  fixes ats :: "('f,string) lp_iterm list"
    and hs :: "('f,string) term list"
    and r :: "string \<Rightarrow> string"
  assumes mgu: "lpc_mgu_resolve (LPIFun f ats) gs (Fun f hs) bs \<sigma> \<rho>"
    and injective: "inj_on r H"
    and positions: "\<And>i. i<length hs \<Longrightarrow>
      (\<exists>x\<in>H. hs!i=Var x \<and> ats!i=LPIVar (r x)) \<or>
      (vars_term (hs!i) \<inter> H = {} \<and>
       (lp_seg_ground (ats!i) \<or> (\<exists>v. ats!i=LPIVar v \<and> v\<notin>r ` H)))"
  defines "D \<equiv> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  shows "lpc_free_knowledge ((H \<inter> D) \<union> lpc_body_only_variables (Fun f hs) bs) \<rho>"
proof -
  let ?B = "lpc_body_only_variables (Fun f hs) bs"
  let ?F = "(H \<inter> D) \<union> ?B"
  let ?tau = "\<lambda>v. if v\<in>r ` H then LPIVar (inv_into H r v) else \<sigma> v"
  let ?nu = "\<lambda>x. if x\<in>H\<union>?B then LPIVar x else \<rho> x"
  have unifier: "lp_isubst (LPIFun f ats) \<sigma> = lp_ieval (Fun f hs) \<rho>"
    using mgu by (simp add: lpc_mgu_resolve_def)
  have absent: "?B \<inter> vars_term (Fun f hs) = {}"
    by (auto simp: lpc_body_only_variables_def)
  have comparison: "lp_isubst (LPIFun f ats) ?tau = lp_ieval (Fun f hs) ?nu"
    by (rule lpc_independent_head_comparison[OF unifier injective absent positions])
  have body: "?F \<subseteq> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    by (auto simp: D_def lpc_body_only_variables_def)
  have free: "lpc_free_knowledge ?F ?nu"
    by (auto simp: lpc_free_knowledge_def inj_on_def)
  show ?thesis by (rule lpc_mgu_free_block_from_comparison[OF mgu comparison body free])
qed

definition lpc_head_link_value where
  "lpc_head_link_value links x = the_default x (map_of links x)"

definition lpc_check_head_links where
  "lpc_check_head_links F G ts hs links =
    (let H=set (map fst links); v=lpc_head_link_value links in
      length ts=length hs \<and> v ` H \<subseteq> set F \<and> inj_on v H \<and>
      list_all (\<lambda>i.
        (case hs!i of Var x \<Rightarrow> x\<in>H \<and> ts!i=Var (v x) | _ \<Rightarrow> False) \<or>
        (vars_term (hs!i) \<inter> H = {} \<and>
          (vars_term (ts!i) \<subseteq> set G \<or>
           (case ts!i of Var x \<Rightarrow> x\<in>set F \<and> x\<notin>v ` H | _ \<Rightarrow> False))))
        [0..<length hs])"

theorem lpc_checked_head_links_knowledge:
  fixes ts hs :: "('f,string) term list"
    and \<eta> :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve (lp_ieval (Fun f ts) \<eta>) gs (Fun f hs) bs \<sigma> \<rho>"
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
    by (rule lpc_mgu_independent_head_knowledge[OF _ ri positions]) (use mgu in simp)
qed

fun lpc_head_link_candidate where
  "lpc_head_link_candidate F (Var x,Var y) = (if x\<in>set F then [(y,x)] else [])"
| "lpc_head_link_candidate F _ = []"

definition lpc_result_free_variables where
  "lpc_result_free_variables F G a h bs =
    (case (a,h) of (Fun f ts,Fun g hs) \<Rightarrow>
      (let links=concat (map (lpc_head_link_candidate F) (zip ts hs)) in
        if f=g \<and> lpc_check_head_links F G ts hs links then
          (set (map fst links) \<inter>
            set (concat (map (\<lambda>g. concat (map lpc_term_variable_list (lp_cut_terms g))) bs)))
          \<union> lpc_body_only_variables h bs
        else lpc_body_only_variables h bs)
    | _ \<Rightarrow> lpc_body_only_variables h bs)"

theorem lpc_result_free_variables_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a \<eta>) gs h bs \<sigma> \<rho>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
  shows "lpc_free_knowledge (lpc_result_free_variables F G a h bs) \<rho>"
proof (cases a)
  case (Var x)
  then show ?thesis using lpc_mgu_body_only_knowledge[OF mgu]
    by (simp add: lpc_result_free_variables_def split: term.splits)
next
  case A: (Fun f ts)
  show ?thesis
  proof (cases h)
    case (Var x)
    then show ?thesis using A lpc_mgu_body_only_knowledge[OF mgu]
      by (simp add: lpc_result_free_variables_def)
  next
    case H: (Fun g hs)
    let ?links = "concat (map (lpc_head_link_candidate F) (zip ts hs))"
    show ?thesis
    proof (cases "f=g \<and> lpc_check_head_links F G ts hs ?links")
      case True
      have mg: "lpc_mgu_resolve (lp_ieval (Fun f ts) \<eta>) gs (Fun f hs) bs \<sigma> \<rho>"
        using mgu A H True by simp
      have chk: "lpc_check_head_links F G ts hs ?links" using True by simp
      have fact: "lpc_free_knowledge
        ((set (map fst ?links) \<inter> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t))
          \<union> lpc_body_only_variables (Fun f hs) bs) \<rho>"
        by (rule lpc_checked_head_links_knowledge[OF mg chk free ground])
      show ?thesis using fact A H True
        by (simp add: lpc_result_free_variables_def Let_def)
    next
      case False
      then show ?thesis using A H lpc_mgu_body_only_knowledge[OF mgu]
        by (simp add: lpc_result_free_variables_def Let_def; blast)
    qed
  qed
qed

lemma lpc_result_free_variables_finite:
  "finite (lpc_result_free_variables F G a h bs)"
  by (auto simp: lpc_result_free_variables_def Let_def lpc_body_only_variables_def split: term.splits)

definition lpc_mgu_result_free where
  "lpc_mgu_result_free F G a h bs l = map (lp_prefix l)
    (sorted_list_of_set (lpc_result_free_variables F G a h bs))"

lemma lpc_mgu_result_free_sound:
  assumes mgu: "lpc_mgu_resolve (lp_ieval a \<eta>) gs h bs \<sigma> \<rho>"
    and free: "lpc_free_knowledge (set F) \<eta>"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (\<eta> x)"
  shows "lpc_free_knowledge (set (lpc_mgu_result_free F G a h bs l))
    (lp_cut_resolution_env k l \<eta> \<sigma> \<rho>)"
proof -
  let ?F = "lpc_result_free_variables F G a h bs"
  have known: "lpc_free_knowledge ?F \<rho>"
    by (rule lpc_result_free_variables_sound[OF mgu free ground])
  have env: "\<And>x. lp_cut_resolution_env k l \<eta> \<sigma> \<rho> (lp_prefix l x) = \<rho> x"
    by (simp add: lp_cut_resolution_env_def lp_prefix_def)
  have source: "set (lpc_mgu_result_free F G a h bs l) = lp_prefix l ` ?F"
    by (simp add: lpc_mgu_result_free_def lpc_result_free_variables_finite)
  show ?thesis using known
    by (auto simp: source lpc_free_knowledge_def inj_on_def env)
qed

end
