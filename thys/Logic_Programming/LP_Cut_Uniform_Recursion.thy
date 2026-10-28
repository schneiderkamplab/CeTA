theory LP_Cut_Uniform_Recursion
  imports LP_Cut_NO_Pumping
begin

text \<open>A first, universally matching clause can recurse with changing
arguments forever. This is an ordered-source rule, not an inference from a DP
loop. Ground arguments prevent substitutions from invalidating later iterations.\<close>

lemma lpc_uniform_ground_eval:
  assumes "\<And>x. x\<in>vars_term t \<Longrightarrow> lp_seg_ground (rho x)"
  shows "lp_seg_ground (lp_ieval t rho)"
  using assms by (induct t) (auto simp: list_all_iff intro: lp_seg_ground.intros)

lemma lpc_uniform_head_mgu:
  assumes ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
    and vars: "vars_term b \<subseteq> set xs"
  shows "lpc_mgu_resolve (lp_ieval (Fun f (map Var xs)) rho) []
    (Fun f (map Var xs)) [LPCAtom b] LPIVar rho"
proof -
  have head_ground: "lp_seg_ground (lp_ieval (Fun f (map Var xs)) rho)"
    by (rule lpc_uniform_ground_eval) (use ground in auto)
  have body_ground: "lp_seg_ground (lp_ieval b rho)"
    by (rule lpc_uniform_ground_eval) (use ground vars in auto)
  have body: "lp_ieval b rho = lp_ieval b nu"
    if eq: "lp_isubst (lp_ieval (Fun f (map Var xs)) rho) tau =
      lp_ieval (Fun f (map Var xs)) nu" for tau nu
  proof (rule lp_ieval_cong)
    fix x assume "x\<in>vars_term b"
    then have "x\<in>set xs" using vars by auto
    moreover have same: "lp_ieval (Fun f (map Var xs)) rho = lp_ieval (Fun f (map Var xs)) nu"
      using eq by (simp only: lp_seg_ground_subst[OF head_ground])
    ultimately show "rho x=nu x" by (auto intro: lpc_ieval_variables_eq[OF same])
  qed
  show ?thesis
    unfolding lpc_mgu_resolve_def
    using head_ground body_ground body
    by (auto simp: lp_seg_ground_subst)
qed

lemma lpc_uniform_values:
  assumes "distinct xs" "length ys=length xs"
  shows "\<exists>rho. map rho xs=ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then obtain y zs where ys: "ys=y#zs" by (cases ys) auto
  obtain rho where rho: "map rho xs=zs" using Cons.hyps Cons.prems ys by auto
  have "map (rho(x:=y)) xs=zs" using rho Cons.prems by (auto intro!: map_cong)
  then have "map (rho(x:=y)) (x#xs)=y#zs"
    by (simp add: fun_upd_def)
  then show ?case using ys by (intro exI[where x="rho(x:=y)"]) (simp add: fun_upd_def)
qed

lemma lpc_uniform_fresh:
  "\<exists>m. lp_cut_fresh m s"
proof -
  let ?S = "\<Union>e\<in>set s. lp_cut_entry_scopes e"
  let ?m = "Suc (Lattices_Big.linorder_class.Max (insert (0::nat) ?S))"
  have finite: "finite (insert (0::nat) ?S)" using lpc_no_scopes_finite[of s] by simp
  have "?m\<notin>?S"
  proof
    assume "?m\<in>?S"
    then have "?m\<le>Lattices_Big.linorder_class.Max (insert 0 ?S)"
      by (intro Max_ge[OF finite]) simp
    then show False by simp
  qed
  then show ?thesis by (auto simp: lp_cut_fresh_def)
qed

lemma lpc_uniform_iteration:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),[LPCAtom (Fun (LPCUser f) us)])"
    and distinct: "distinct xs" and length: "length us=length xs"
    and vars: "vars_term (Fun (LPCUser f) us) \<subseteq> set xs"
    and ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
  shows "\<exists>rho' es'. (\<forall>x\<in>set xs. lp_seg_ground (rho' x)) \<and>
    (LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es,
     LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho')]#es')
       \<in>(lp_cut_mgu_source P)\<^sup>+"
proof -
  let ?a = "lp_ieval (Fun (LPCUser f) (map Var xs)) rho"
  let ?s = "LPCGoals [LPCAtom ?a]#es"
  obtain m where fresh: "lp_cut_fresh m ?s" using lpc_uniform_fresh by blast
  let ?es = "map (\<lambda>d. LPCClause [LPCAtom ?a] d m) cs @ LPCBarrier m#es"
  have fresh': "lp_cut_fresh m (LPCGoals [LPCAtom (LPIFun (LPCUser f) (map rho xs))]#es)"
    using fresh by (simp add: o_def)
  have case_step: "(?s,LPCClause [LPCAtom ?a] c m#?es)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.case_call[OF fresh', where P=P]
    by (simp add: first o_def)
  have mgu: "lpc_mgu_resolve ?a [] (fst (P!c)) (snd (P!c)) LPIVar rho"
    using lpc_uniform_head_mgu[OF ground vars] by (simp add: clause)
  have resolve: "(LPCClause [LPCAtom ?a] c m#?es,
      LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) us) rho)]#?es)\<in>lp_cut_mgu_source P"
    using lp_cut_mgu_source.resolve[OF index mgu, of m ?es]
    by (simp add: clause)
  obtain rho' where valuation: "map rho' xs=map (\<lambda>t. lp_ieval t rho) us"
    using lpc_uniform_values[OF distinct, of "map (\<lambda>t. lp_ieval t rho) us"] length by auto
  have same: "lp_ieval (Fun (LPCUser f) (map Var xs)) rho'=lp_ieval (Fun (LPCUser f) us) rho"
    using valuation by (simp add: o_def)
  have grounds: "\<forall>x\<in>set xs. lp_seg_ground (rho' x)"
  proof -
    have "\<forall>t\<in>set us. lp_seg_ground (lp_ieval t rho)"
      using vars ground by (auto intro!: lpc_uniform_ground_eval)
    then have "\<forall>v\<in>set (map rho' xs). lp_seg_ground v" unfolding valuation by auto
    then show ?thesis by auto
  qed
  show ?thesis
    by (intro exI[where x=rho'] exI[where x="?es"] conjI[OF grounds])
      (use trancl_trans[OF r_into_trancl[OF case_step] r_into_trancl[OF resolve]] same in simp)
qed

theorem lpc_uniform_recursion_nontermination:
  assumes first: "lp_cut_slice P (LPCUser f) (length xs)=c#cs"
    and index: "c<length P"
    and clause: "P!c=(Fun (LPCUser f) (map Var xs),[LPCAtom (Fun (LPCUser f) us)])"
    and distinct: "distinct xs" and length: "length us=length xs"
    and vars: "vars_term (Fun (LPCUser f) us) \<subseteq> set xs"
    and ground: "\<And>x. x\<in>set xs \<Longrightarrow> lp_seg_ground (rho x)"
  shows "\<not>SN_on (lp_cut_mgu_source P)
    {LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es}"
proof -
  let ?X = "{s. \<exists>rho es. (\<forall>x\<in>set xs. lp_seg_ground (rho x)) \<and>
      s=LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es}"
  have member: "LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) (map Var xs)) rho)]#es\<in>?X"
    using ground by auto
  have successor: "\<exists>t\<in>?X. (s,t)\<in>(lp_cut_mgu_source P)\<^sup>+" if "s\<in>?X" for s
    using that lpc_uniform_iteration[OF first index clause distinct length vars] by blast
  have serial: "\<forall>s\<in>?X. \<exists>t\<in>?X. (s,t)\<in>(lp_cut_mgu_source P)\<^sup>+"
    using successor by blast
  show ?thesis using lower_set_imp_not_SN_on[OF member serial] SN_on_trancl by blast
qed

end
