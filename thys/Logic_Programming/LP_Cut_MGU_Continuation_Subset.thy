theory LP_Cut_MGU_Continuation_Subset
 imports LP_Cut_Most_General_Source
begin

text \<open>Project a consequence of the same actual MGU onto selected observed
continuation goals. This does not remove goals or branches from execution.\<close>

lemma lpc_mgu_unify_continuation_subset:
 assumes mgu: "lpc_mgu_unify a b gs sigma"
 and subset: "set observed \<subseteq> set gs"
 shows "lpc_mgu_unify a b observed sigma"
 unfolding lpc_mgu_unify_def
proof (intro conjI allI impI)
 show "lp_isubst a sigma=lp_isubst b sigma"
  using mgu by (simp add: lpc_mgu_unify_def)
next
 fix tau :: "string \<Rightarrow> ('a,string) lp_iterm"
 assume unifies: "lp_isubst a tau=lp_isubst b tau"
 obtain delta where atom: "lp_isubst (lp_isubst a sigma) delta=lp_isubst a tau"
 and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
   map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
  using mgu unifies unfolding lpc_mgu_unify_def by blast
 show "\<exists>delta. lp_isubst (lp_isubst a sigma) delta=lp_isubst a tau \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) observed =
   map (lp_cut_map (\<lambda>t. lp_isubst t tau)) observed"
  by (rule exI[of _ delta]) (use atom goals subset in \<open>auto simp: map_eq_conv\<close>)
qed

ML \<open>
val checked = @{thms lpc_mgu_unify_continuation_subset};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted MGU continuation projection" else ();
\<close>
end
