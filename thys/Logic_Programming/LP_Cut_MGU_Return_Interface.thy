theory LP_Cut_MGU_Return_Interface
 imports LP_Cut_NO_Continuation_Steps LP_Cut_Return_State
begin

text \<open>Most-generality must cover the tracked return interface as well as
active goals. Agreement on that finite interface extends to every continuation
expressed through it. The shared return environment has a fixed ground value
outside the interface, so those positions introduce no hidden variables.\<close>

lemma lpc_return_env_substitution_agreement:
 assumes observed: "map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) payload =
   map (\<lambda>t. lp_isubst (lp_ieval t eta) comparison_subst) payload"
 shows "lp_isubst (lp_isubst (lpc_return_env payload eta n) sigma) delta =
   lp_isubst (lpc_return_env payload eta n) comparison_subst"
proof (cases "n < length payload")
 case True
 note same = arg_cong[OF observed, of "\<lambda>xs. xs!n"]
 show ?thesis using same True by (simp add: lpc_return_env_def)
next
 case False then show ?thesis by (simp add: lpc_return_env_def)
qed

lemma lpc_return_term_substitution_agreement:
 assumes observed: "map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) payload =
   map (\<lambda>t. lp_isubst (lp_ieval t eta) comparison_subst) payload"
 shows "lp_isubst (lp_isubst (lp_ieval t (lpc_return_env payload eta)) sigma) delta =
   lp_isubst (lp_ieval t (lpc_return_env payload eta)) comparison_subst"
 unfolding lp_ieval_subst
 by (rule lp_ieval_cong) (use lpc_return_env_substitution_agreement[OF observed] in simp)

lemma lpc_return_goals_substitution_agreement:
 assumes goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
   (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) =
   map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
   (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload)"
 shows "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) =
   map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)"
proof -
   have active: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs =
       map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst)) gs"
     using arg_cong[OF goals, of "take (length gs)"] by simp
   have observed_goals: "map (\<lambda>t. LPCAtom (lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta)) payload =
       map (\<lambda>t. LPCAtom (lp_isubst (lp_ieval t eta) comparison_subst)) payload"
     using arg_cong[OF goals, of "drop (length gs)"] by (simp add: map_map o_def)
   have observed: "map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) payload =
       map (\<lambda>t. lp_isubst (lp_ieval t eta) comparison_subst) payload"
     using arg_cong[OF observed_goals, of "map (\<lambda>g. case g of LPCAtom t \<Rightarrow> t | _ \<Rightarrow> LPIFun LPCTruth [])"]
     by (simp add: map_map o_def)
   have continuation: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
       (map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) =
       map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
       (map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)"
     unfolding map_map o_def lp_cut_map_comp
     by (rule map_cong[OF refl], rule lp_cut_goal_map_cong)
       (use lpc_return_term_substitution_agreement[OF observed] in simp)
 show ?thesis by (simp only: map_append active continuation)
qed

lemma lpc_mgu_resolve_return_continuation:
 fixes a :: "('f lp_cut_symbol,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve a
   (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) h bs sigma rho"
 shows "lpc_mgu_resolve a
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)
   h bs sigma rho"
proof -
 have unifies: "lp_isubst a sigma = lp_ieval h rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have factor: "\<exists>delta.
   lp_isubst (lp_isubst a sigma) delta = lp_isubst a comparison_subst \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
     (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) =
   map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
     (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs =
     map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
   if equation: "lp_isubst a comparison_subst = lp_ieval h nu"
   for comparison_subst nu :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 proof -
   obtain delta where atom: "lp_isubst (lp_isubst a sigma) delta = lp_isubst a comparison_subst"
     and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
       (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) =
       map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
       (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload)"
     and body: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs =
       map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
     using mgu equation unfolding lpc_mgu_resolve_def by blast
   note lifted = lpc_return_goals_substitution_agreement[OF goals, of rest]
   show ?thesis by (rule exI[of _ delta]) (use atom lifted body in blast)
 qed
 show ?thesis using unifies factor unfolding lpc_mgu_resolve_def by blast
qed

lemma lpc_mgu_unify_return_continuation:
 fixes a b :: "('f lp_cut_symbol,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify a b
   (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) sigma"
 shows "lpc_mgu_unify a b
   (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) sigma"
 unfolding lpc_mgu_unify_def
proof (intro conjI allI impI)
 show "lp_isubst a sigma = lp_isubst b sigma"
   using mgu by (simp add: lpc_mgu_unify_def)
next
 fix comparison_subst :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
 assume equation: "lp_isubst a comparison_subst = lp_isubst b comparison_subst"
 obtain delta where atom: "lp_isubst (lp_isubst a sigma) delta = lp_isubst a comparison_subst"
   and goals: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
     (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload) =
     map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
     (gs @ map (\<lambda>t. LPCAtom (lp_ieval t eta)) payload)"
   using mgu equation unfolding lpc_mgu_unify_def by blast
 note lifted = lpc_return_goals_substitution_agreement[OF goals, of rest]
 show "\<exists>delta. lp_isubst (lp_isubst a sigma) delta = lp_isubst a comparison_subst \<and>
   map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
     (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest) =
   map (lp_cut_map (\<lambda>t. lp_isubst t comparison_subst))
     (gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)"
   by (rule exI[of _ delta]) (use atom lifted in blast)
qed

ML \<open>
val checked = [@{thm lpc_return_env_substitution_agreement},
 @{thm lpc_return_term_substitution_agreement}, @{thm lpc_mgu_resolve_return_continuation},
 @{thm lpc_mgu_unify_return_continuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return interface MGU dependency" else ();
\<close>
end
