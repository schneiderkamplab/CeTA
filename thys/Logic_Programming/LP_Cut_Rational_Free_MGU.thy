theory LP_Cut_Rational_Free_MGU
  imports LP_Cut_Rational_Free_Equality
begin

text \<open>Existence of a rational unifier is insufficient for a source NO.
The binding below must be most general on the entire active continuation.
Saved alternatives remain outside this substitution, as in the shared source
machine. No finite-tree or finite-spine property follows from this binding.\<close>

lemma lpc_rational_bind_factor:
  assumes solution: "eta x = LPIFun f (map (\<lambda>u. lp_isubst u eta) roots)"
  shows "lp_isubst (lpc_rational_bind x f roots t) eta = lp_isubst t eta"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (use solution in \<open>auto simp: list_all2_conv_all_nth split: lp_iterm.splits if_splits\<close>)

definition lpc_rational_binding where
  "lpc_rational_binding x f roots y =
    (if x=y then LPIFun f (map (lpc_rational_bind x f roots) roots) else LPIVar y)"

lemma lpc_rational_binding_apply:
  "lp_isubst t (lpc_rational_binding x f roots) = lpc_rational_bind x f roots t"
  unfolding lpc_rational_binding_def by (rule lpc_rational_bind_substitution)

lemma lpc_rational_binding_unifies:
  "lp_isubst (LPIVar x) (lpc_rational_binding x f roots) =
   lp_isubst (LPIFun f roots) (lpc_rational_binding x f roots)"
  by (simp add: lpc_rational_binding_apply)

lemma lpc_rational_binding_factor:
  assumes solution: "lp_isubst (LPIVar x) eta = lp_isubst (LPIFun f roots) eta"
  shows "lp_isubst (lp_isubst t (lpc_rational_binding x f roots)) eta = lp_isubst t eta"
  unfolding lpc_rational_binding_apply
  by (rule lpc_rational_bind_factor) (use solution in simp)

theorem lpc_rational_binding_most_general:
  "lpc_mgu_unify (LPIVar x) (LPIFun f roots) gs (lpc_rational_binding x f roots)"
  unfolding lpc_mgu_unify_def
proof (intro conjI allI impI)
  show "lp_isubst (LPIVar x) (lpc_rational_binding x f roots) =
    lp_isubst (LPIFun f roots) (lpc_rational_binding x f roots)"
    by (rule lpc_rational_binding_unifies)
next
  fix tau :: "string \<Rightarrow> ('a,string) lp_iterm"
  assume solution: "lp_isubst (LPIVar x) tau = lp_isubst (LPIFun f roots) tau"
  show "\<exists>delta.
    lp_isubst (lp_isubst (LPIVar x) (lpc_rational_binding x f roots)) delta = lp_isubst (LPIVar x) tau \<and>
    map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t (lpc_rational_binding x f roots)) delta)) gs =
    map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
    by (rule exI[of _ tau]) (simp only: lpc_rational_binding_factor[OF solution]; simp)
qed


theorem lpc_rational_binding_source_step:
  "(LPCGoals (LPCUnify (LPIVar x) (LPIFun f roots)#gs)#es,
    LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t (lpc_rational_binding x f roots))) gs)#es)
    \<in>lp_cut_mgu_source P"
  by (rule lp_cut_mgu_source.unify[OF lpc_rational_binding_most_general])

ML \<open>
val checked = [@{thm lpc_rational_binding_most_general}, @{thm lpc_rational_binding_source_step}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm lpc_free_runtime_variable_unifies}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn name => not (member (op =) inherited name)) (oracles checked)
  then error "Untrusted rational MGU dependency" else ();
\<close>
end
