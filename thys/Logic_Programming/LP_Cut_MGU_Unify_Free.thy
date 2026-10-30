theory LP_Cut_MGU_Unify_Free
  imports LP_Cut_MGU_Context_Free
begin

lemma lpc_mgu_unify_context_factor:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma tau :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
    and comparison: "lp_isubst (lp_ieval a eta) tau=lp_isubst (lp_ieval b eta) tau"
  shows "\<exists>delta :: string \<Rightarrow> ('f,string) lp_iterm.
    \<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
proof -
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
     map (lp_cut_map (\<lambda>t. lp_isubst t tau)) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    using mgu comparison unfolding lpc_mgu_unify_def by blast
  show ?thesis
  proof (rule exI[of _ delta], intro ballI)
    fix g t x assume g: "g\<in>set gs" and t: "t\<in>set (lp_cut_terms g)" and x: "x\<in>vars_term t"
    have mapped: "lp_cut_map (\<lambda>u. lp_isubst (lp_isubst (lp_ieval u eta) sigma) delta) g =
      lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u eta) tau) g"
      using factor g by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
    have "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta=lp_isubst (lp_ieval t eta) tau"
      using mapped t by (cases g) auto
    then show "lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) tau"
      using lpc_ieval_variables_eq[OF _ x] by (simp add: lp_ieval_subst)
  qed
qed

lemma lpc_mgu_unify_untouched_context_free:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
    and sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
    and free: "lpc_free_knowledge F eta"
    and ground: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and vars: "vars_term a \<union> vars_term b \<subseteq> G\<union>F"
    and subset: "C\<subseteq>F"
    and disjoint: "C\<inter>(vars_term a \<union> vars_term b)={}"
    and occurs: "C\<subseteq>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  shows "lpc_free_knowledge C (\<lambda>x. lp_isubst (eta x) sigma)"
proof -
  obtain r where inj: "inj_on r F" and repr: "\<forall>x\<in>F. eta x=LPIVar (r x)"
    using lpc_free_knowledge_representation[OF free] by blast
  let ?tau = "\<lambda>y. if y\<in>r ` C then LPIVar y else sigma y"
  have same: "lp_isubst (eta x) ?tau=lp_isubst (eta x) sigma" if x: "x\<in>vars_term a \<union> vars_term b" for x
  proof (cases "x\<in>G")
    case True
    then show ?thesis using ground by (simp add: lp_seg_ground_subst)
  next
    case False
    have f: "x\<in>F" using vars x False by blast
    have n: "r x\<notin>r ` C"
    proof
      assume "r x\<in>r ` C"
      then obtain y where y: "y\<in>C" and eq: "r x=r y" by blast
      have yf: "y\<in>F" using subset y by blast
      have "x=y" by (rule inj_onD[OF inj eq f yf])
      then have "x\<in>C" using y by simp
      then show False using disjoint x by blast
    qed
    show ?thesis using repr f n by simp
  qed
  have comparison: "lp_isubst (lp_ieval a eta) ?tau=lp_isubst (lp_ieval b eta) ?tau"
  proof -
    have left: "lp_isubst (lp_ieval a eta) ?tau=lp_isubst (lp_ieval a eta) sigma"
      unfolding lp_ieval_subst by (rule lp_ieval_cong) (use same in auto)
    have right: "lp_isubst (lp_ieval b eta) ?tau=lp_isubst (lp_ieval b eta) sigma"
      unfolding lp_ieval_subst by (rule lp_ieval_cong) (use same in auto)
    show ?thesis using mgu left right by (simp add: lpc_mgu_unify_def)
  qed
  obtain delta :: "string \<Rightarrow> ('f,string) lp_iterm" where factor:
    "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
      lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) ?tau"
    using lpc_mgu_unify_context_factor[OF mgu comparison] by blast
  have equation: "lp_isubst (lp_isubst (eta x) sigma) delta=eta x" if x: "x\<in>C" for x
  proof -
    have "lp_isubst (lp_isubst (eta x) sigma) delta=lp_isubst (eta x) ?tau"
      using factor occurs x by blast
    then show ?thesis using repr subset x by auto
  qed
  have variables: "\<forall>x\<in>C. \<exists>y. lp_isubst (eta x) sigma=LPIVar y"
  proof (intro ballI)
    fix x assume x: "x\<in>C"
    have val_eq: "eta x=LPIVar (r x)" using repr subset x by blast
    have "lp_isubst (lp_isubst (eta x) sigma) delta=LPIVar (r x)"
      using equation[OF x] val_eq by simp
    then show "\<exists>y. lp_isubst (eta x) sigma=LPIVar y"
      by (rule lpc_isubst_variable_reflect)
  qed
  have distinct: "inj_on (\<lambda>x. lp_isubst (eta x) sigma) C"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>C" and y: "y\<in>C" and eq: "lp_isubst (eta x) sigma=lp_isubst (eta y) sigma"
    have old_eq: "eta x=eta y"
    proof -
      have "eta x=lp_isubst (lp_isubst (eta x) sigma) delta" by (rule sym[OF equation[OF x]])
      also have "...=lp_isubst (lp_isubst (eta y) sigma) delta" by (rule arg_cong[OF eq])
      also have "...=eta y" by (rule equation[OF y])
      finally show ?thesis .
    qed
    have eta_inj: "inj_on eta F" using free unfolding lpc_free_knowledge_def by (rule conjunct2)
    have xf: "x\<in>F" using subset x by blast
    have yf: "y\<in>F" using subset y by blast
    show "x=y" by (rule inj_onD[OF eta_inj old_eq xf yf])
  qed
  show ?thesis using variables distinct by (simp add: lpc_free_knowledge_def)
qed


definition lpc_unify_free_candidates where
  "lpc_unify_free_candidates F a b gs k = filter (\<lambda>x.
    length x<k \<and> x \<notin> vars_term a  \<union>  vars_term b \<and>
    list_ex (\<lambda>g. list_ex (\<lambda>t. x \<in> vars_term t) (lp_cut_terms g)) gs) F"

definition lpc_unify_untouched_free where
  "lpc_unify_untouched_free F G a b gs k =
    (if vars_term a  \<union>  vars_term b  \<subseteq>  set G  \<union>  set F
     then map (lp_prefix k) (lpc_unify_free_candidates F a b gs k) else [])"

lemma lpc_unify_untouched_free_sound:
  assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
    and ground: "\<forall>x \<in> set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
    and bounds: "2 * k  \<le>  l"
  shows "lpc_free_knowledge (set (lpc_unify_untouched_free F G a b gs k))
    (lp_cut_resolution_env k l eta sigma eta)"
proof (cases "vars_term a  \<union>  vars_term b  \<subseteq>  set G  \<union>  set F")
  case False
  have empty: "lpc_unify_untouched_free F G a b gs k=[]"
    unfolding lpc_unify_untouched_free_def by (rule if_not_P[OF False])
  show ?thesis by (simp only: empty list.set) (simp add: lpc_free_knowledge_def)
next
  case True
  let ?C="set (lpc_unify_free_candidates F a b gs k)"
  let ?value="\<lambda>x. lp_isubst (eta x) sigma"
  let ?env="lp_cut_resolution_env k l eta sigma eta"
  have subset: "?C \<subseteq> set F" and disjoint: "?C \<inter> (vars_term a  \<union>  vars_term b)={}"
    and occurs: "?C \<subseteq> (\<Union>g \<in> set gs. \<Union>t \<in> set (lp_cut_terms g). vars_term t)"
    by (auto simp: lpc_unify_free_candidates_def list_ex_iff)
  have known: "lpc_free_knowledge ?C ?value"
    by (rule lpc_mgu_unify_untouched_context_free[OF mgu free ground True subset disjoint occurs])
  have env: "?env (lp_prefix k x)=?value x" if x: "x \<in> ?C" for x
  proof -
    have short: "length x<k" using x by (simp add: lpc_unify_free_candidates_def)
    have upper: " \<not> l \<le> k+length x" using short bounds by arith
    show ?thesis by (simp add: lp_cut_resolution_env_def lp_prefix_def upper)
  qed
  have variables: "\<forall>x \<in> lp_prefix k ` ?C. \<exists>v. ?env x=LPIVar v"
    using known env by (auto simp: lpc_free_knowledge_def)
  have injective: "inj_on ?env (lp_prefix k ` ?C)"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> lp_prefix k ` ?C" and y: "y \<in> lp_prefix k ` ?C"
      and eq: "?env x=?env y"
    obtain u v where u: "u \<in> ?C" "x=lp_prefix k u" and v: "v \<in> ?C" "y=lp_prefix k v"
      using x y by blast
    have same: "?value u=?value v" using eq env[OF u(1)] env[OF v(1)] u(2) v(2) by simp
    have inj: "inj_on ?value ?C" using known by (simp add: lpc_free_knowledge_def)
    have "u=v" by (rule inj_onD[OF inj same u(1) v(1)])
    then show "x=y" using u v by simp
  qed
  show ?thesis using True variables injective
    by (simp add: lpc_unify_untouched_free_def lpc_free_knowledge_def)
qed

ML \<open>
val checked = [@{thm lpc_unify_untouched_free_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted equality free-knowledge dependency" else ();
\<close>
end
