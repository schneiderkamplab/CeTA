theory LP_Prolog_Matching_Structure
 imports LP_Prolog_Finite_Matching_Head LP_Cut_MGU_Variants LP_Prolog_Constructor_Arguments
begin

text \<open>A finite runtime call has an ordinary finite template. Matching-head
resolution preserves that template up to an injective renaming, not equality of
old and refreshed runtime values. Sharing is retained by the same renaming.\<close>

lemma lpp_finite_runtime_template:
 fixes t :: "('f,'v) lp_iterm"
 assumes finite: "lpp_finite_term t"
 shows "\<exists>s. t=lp_ieval s LPIVar"
 using finite
proof (induct rule: lpp_finite_term.induct)
 case (variable x)
 show ?case by (rule exI[of _ "Var x"]) simp
next
 case (node ts f)
 define template_of :: "('f,'v) lp_iterm \<Rightarrow> ('f,'v) term"
  where "template_of t = (SOME s. t=lp_ieval s LPIVar)" for t
 have chosen: "t=lp_ieval (template_of t) LPIVar" if "t\<in>set ts" for t
  unfolding template_of_def by (rule someI_ex) (use node.hyps that in \<open>simp add: list_all_iff\<close>)
 have mapped: "map (\<lambda>t. lp_ieval (template_of t) LPIVar) ts=ts"
  by (rule map_idI) (use chosen in simp)
 show ?case by (rule exI[of _ "Fun f (map template_of ts)"]) (simp add: map_map o_def mapped)
qed

theorem lpp_matching_head_preserves_structure:
 assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
 and matching: "lp_ieval h nu=a"
 and finite: "lpp_finite_term a"
 shows "\<exists>template rename. a=lp_ieval template LPIVar \<and>
   inj_on rename (vars_term template) \<and>
   lp_ieval h rho=lp_ieval template (LPIVar \<circ> rename)"
proof -
 obtain template where initial: "a=lp_ieval template LPIVar"
  using lpp_finite_runtime_template[OF finite] by blast
 have comparison: "lp_isubst a LPIVar=lp_ieval h nu" using matching by simp
 obtain delta where raw: "lp_isubst (lp_isubst a sigma) delta=lp_isubst a LPIVar"
  using mgu comparison unfolding lpc_mgu_resolve_def by blast
 have factor: "lp_isubst (lp_isubst a sigma) delta=a" using raw by simp
 have roundtrip: "lp_isubst (lp_ieval t sigma) delta=lp_ieval t LPIVar"
  if "t\<in>set [template]" for t
  using factor initial that by (simp add: lp_ieval_subst)
 obtain rename where injective: "inj_on rename (vars_term template)"
 and preserved: "lp_ieval template sigma=lp_ieval template (LPIVar \<circ> rename)"
  using lpc_finite_roundtrip_renaming[where ts="[template]", OF roundtrip] by auto
 have resolved: "lp_ieval h rho=lp_isubst a sigma"
  using mgu by (simp add: lpc_mgu_resolve_def)
 show ?thesis using initial injective preserved resolved
  by (intro exI[of _ template] exI[of _ rename]) (simp add: lp_ieval_subst)
qed

lemma lpp_checked_matching_preserves_structure:
 assumes checked: "lp_cut_check_match call head bindings"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta) gs head bs sigma rho"
 and finite: "lpp_finite_term (lp_ieval call eta)"
 shows "\<exists>template rename. lp_ieval call eta=lp_ieval template LPIVar \<and>
   inj_on rename (vars_term template) \<and>
   lp_ieval head rho=lp_ieval template (LPIVar \<circ> rename)"
proof -
 have matching: "lp_ieval head (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval call eta"
  using checked unfolding lp_cut_check_match_def
  by (simp add: lp_ieval_finite_subst[symmetric])
 show ?thesis by (rule lpp_matching_head_preserves_structure[OF mgu matching finite])
qed

lemma lpp_constructor_arguments_finite_template:
 assumes observed: "lpp_constructor_arguments value f arguments"
 and finite: "lpp_finite_term value"
 shows "\<exists>children. value=lp_ieval (Fun f children) LPIVar \<and>
   arguments=lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) children)"
proof -
 obtain template where represented: "value=lp_ieval template LPIVar"
  using lpp_finite_runtime_template[OF finite] by blast
 show ?thesis using represented observed
  by (cases template) (auto simp: lpp_constructor_arguments_def)
qed

lemma lpp_structure_renaming_does_not_construct:
 "lp_ieval (Var x) (LPIVar \<circ> rename) \<noteq> LPIFun f ts"
 by simp

lemma lpp_structure_renaming_does_not_merge:
 assumes distinct: "x\<noteq>y" and injective: "inj_on rename {x,y}"
 shows "lp_ieval (Fun f [Var x,Var y]) (LPIVar \<circ> rename) \<noteq> LPIFun f [LPIVar z,LPIVar z]"
 using distinct injective by (auto simp: inj_on_def)

lemma lpp_cyclic_runtime_has_no_finite_template:
 assumes cyclic: "t=LPIFun f [t]"
 shows "\<not>(\<exists>template. t=lp_ieval template LPIVar)"
proof
 assume "\<exists>template. t=lp_ieval template LPIVar"
 then obtain template where represented: "t=lp_ieval template LPIVar" by blast
 have finite: "lpp_finite_term t" unfolding represented by (rule lpp_finite_term_initial)
 show False using lpp_finite_constructor_not_self_child[OF finite, of f] cyclic by contradiction
qed

ML \<open>
val checked = @{thms lpp_finite_runtime_template lpp_matching_head_preserves_structure lpp_checked_matching_preserves_structure
 lpp_constructor_arguments_finite_template lpp_structure_renaming_does_not_construct
 lpp_structure_renaming_does_not_merge lpp_cyclic_runtime_has_no_finite_template};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted matching structure preservation" else ();
\<close>
end
