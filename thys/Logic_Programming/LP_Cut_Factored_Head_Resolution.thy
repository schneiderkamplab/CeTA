theory LP_Cut_Factored_Head_Resolution
 imports LP_Cut_Fresh_Head_Resolution
begin

text \<open>A factored caller unifier and a matching head environment give a
most-general resolution for the entire active continuation. Fresh body locals
remain independent; saved alternatives are not part of the substitution.\<close>

lemma lpc_factored_head_mgu:
 fixes a :: "('f,string) lp_iterm"
 assumes variables: "set xs=vars_term h"
   and matching: "lp_isubst a mu=lp_ieval h eta"
   and preserves: "\<And>tau nu :: string \<Rightarrow> ('f,string) lp_iterm. \<And>x. lp_isubst a tau=lp_ieval h nu \<Longrightarrow>
      lp_isubst (mu x) tau=tau x"
 shows "lpc_mgu_resolve a gs h bs
   (\<lambda>x. lp_isubst (mu x) lpc_fresh_caller)
   (lpc_fresh_head_environment xs eta)"
proof -
 let ?sigma = "\<lambda>x. lp_isubst (mu x) lpc_fresh_caller"
 let ?rho = "lpc_fresh_head_environment xs eta"
 have head: "lp_ieval h ?rho=lp_isubst (lp_ieval h eta) lpc_fresh_caller"
   unfolding lp_ieval_subst
   by (rule lp_ieval_cong) (use variables in \<open>simp add: lpc_fresh_head_environment_def\<close>)
 have equation: "lp_isubst a ?sigma=lp_ieval h ?rho"
   using head matching by (metis lpc_isubst_comp)
 have factor: "\<exists>delta. lp_isubst (lp_isubst a ?sigma) delta=lp_isubst a tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?sigma) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) delta)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
   if unifies: "lp_isubst a tau=lp_ieval h nu" for tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
 proof -
  let ?delta = "lpc_fresh_factor tau nu"
  have caller: "lp_isubst (lp_isubst t ?sigma) ?delta=lp_isubst t tau" for t
    by (simp add: lpc_isubst_comp lpc_fresh_caller_factor lpc_fresh_caller_def preserves[OF unifies])
  have head_equal: "lp_ieval h (\<lambda>x. lp_isubst (eta x) tau)=lp_ieval h nu"
    using unifies
    by (simp add: lp_ieval_subst[symmetric] matching[symmetric] lpc_isubst_comp preserves[OF unifies])
  have known: "lp_isubst (eta x) tau=nu x" if "x\<in>set xs" for x
    by (rule lpc_ieval_variables_eq[OF head_equal]) (use variables that in simp)
  have local: "lp_isubst (?rho x) ?delta=nu x" for x
    by (simp add: lpc_fresh_head_environment_def lpc_fresh_caller_factor lpc_fresh_local_factor known)
  show ?thesis by (rule exI[of _ "?delta"])
    (simp add: caller lp_ieval_subst local)
 qed
 show ?thesis using equation factor unfolding lpc_mgu_resolve_def by blast
qed

ML \<open>
val checked = [@{thm lpc_factored_head_mgu}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted factored source resolution dependency" else ();
\<close>
end
