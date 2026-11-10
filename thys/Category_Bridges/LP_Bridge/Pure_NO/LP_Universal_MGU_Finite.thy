theory LP_Universal_MGU_Finite
  imports LP_Universal_MGU
begin

lemma lp_finite_embedding_injective:
  "lp_ieval s LPIVar=lp_ieval t LPIVar \<Longrightarrow> s=t"
proof (induct s arbitrary: t)
  case (Var x) then show ?case by (cases t) auto
next
  case (Fun f ss)
  obtain g ts where t: "t=Fun g ts" using Fun.prems by (cases t) auto
  have symbol: "f=g" and eq: "map (\<lambda>u. lp_ieval u LPIVar) ss=map (\<lambda>u. lp_ieval u LPIVar) ts"
    using Fun.prems by (simp_all add: t)
  have len: "length ss=length ts" using arg_cong[OF eq, of length] by simp
  have nth: "ss!i=ts!i" if i: "i<length ss" for i
  proof (rule Fun.hyps[OF nth_mem[OF i]])
    show "lp_ieval (ss!i) LPIVar=lp_ieval (ts!i) LPIVar"
      using arg_cong[OF eq, of "\<lambda>xs. xs!i"] i len by simp
  qed
  have "ss=ts" by (rule nth_equalityI[OF len nth])
  then show ?case by (simp add: t symbol)
qed

lemma lp_universal_mgu_finite_factor:
  fixes tau nu :: "string \<Rightarrow> ('f,string) term"
  assumes mgu: "lp_universal_mgu a h sigma rho"
    and match: "lp_atom_subst a tau=lp_atom_subst h nu"
  obtains delta where "\<And>x. sigma x \<cdot> delta=tau x" "\<And>x. rho x \<cdot> delta=nu x"
proof -
  let ?tau = "\<lambda>x. lp_ieval (tau x) LPIVar"
  let ?nu = "\<lambda>x. lp_ieval (nu x) LPIVar"
  have eq: "lp_atom_eval a ?tau=lp_atom_eval h ?nu"
    using arg_cong[OF match, of "\<lambda>a. lp_atom_eval a LPIVar"]
    by (simp add: lp_atom_eval_def lp_atom_subst_def map_map o_def lp_ieval_finite_subst)
  obtain delta where sf: "\<And>x. lp_ieval (sigma x) delta=?tau x"
    and rf: "\<And>x. lp_ieval (rho x) delta=?nu x"
    and dom: "\<And>x. delta x\<in>range ?tau\<union>range ?nu\<union>range LPIVar"
    using mgu eq unfolding lp_universal_mgu_def by blast
  have finite: "\<forall>x. \<exists>u. delta x=lp_ieval u LPIVar"
  proof
    fix x
    consider (left) y where "delta x=lp_ieval (tau y) LPIVar"
      | (right) y where "delta x=lp_ieval (nu y) LPIVar"
      | (variable) y where "delta x=LPIVar y"
      using dom[of x] by blast
    then show "\<exists>u. delta x=lp_ieval u LPIVar"
    proof cases
      case (left y) then show ?thesis by blast
    next
      case (right y) then show ?thesis by blast
    next
      case (variable y) show ?thesis by (rule exI[of _ "Var y"]) (simp add: variable)
    qed
  qed
  obtain d where d: "\<And>x. delta x=lp_ieval (d x) LPIVar"
    using choice[OF finite] by blast
  have sf': "sigma x\<cdot>d=tau x" for x
    by (rule lp_finite_embedding_injective) (simp add: lp_ieval_finite_subst d[symmetric] sf)
  have rf': "rho x\<cdot>d=nu x" for x
    by (rule lp_finite_embedding_injective) (simp add: lp_ieval_finite_subst d[symmetric] rf)
  show thesis by (rule that[OF sf' rf'])
qed

end
