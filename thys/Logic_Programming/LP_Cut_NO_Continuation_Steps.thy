theory LP_Cut_NO_Continuation_Steps
 imports LP_Cut_NO_Steps LP_Cut_Return_Attached_Answers LP_Cut_MGU_Fresh_Resolve
begin

text \<open>A suspended continuation is part of the active unification
interface. Merely projecting a valid source step to a smaller prefix does not
justify attaching it again. The executable MGU checker supplies the stronger
factorization needed below. Saved alternatives remain unchanged.\<close>

lemma lpc_prefix_mgu_can_instantiate_unused_variables:
  "lpc_mgu_unify (LPIFun c []) (LPIFun c []) [] (\<lambda>x. LPIFun c [])"
  by (simp add: lpc_mgu_unify_def)

lemma lpc_prefix_mgu_cannot_instantiate_live_continuation:
  fixes c :: "'f"
  shows "\<not> lpc_mgu_unify (LPIFun c []) (LPIFun c [])
    [LPCUnify (LPIVar ''live'') (LPIFun c [])] (\<lambda>x. LPIFun c [])"
proof
  assume bad: "lpc_mgu_unify (LPIFun c []) (LPIFun c [])
    [LPCUnify (LPIVar ''live'') (LPIFun c [])] (\<lambda>x. LPIFun c [])"
  have all: "\<forall>tau :: string \<Rightarrow> ('f,string) lp_iterm. LPIFun c [] = tau ''live''"
    using bad by (simp add: lpc_mgu_unify_def)
  have "LPIFun c [] = LPIVar ''live''" using all[rule_format, of LPIVar] .
  then show False by simp
qed

lemma lpc_checked_unify_retains_continuation:
  fixes a b :: "('f lp_cut_symbol,string) term"
  assumes checked: "lpc_check_mgu fuel [(a,b)] V images"
  shows "(lp_cut_state_eval (LPCGoals (LPCUnify a b # gs @ rest)#es) LPIVar,
    lp_cut_state_eval (LPCGoals
      (map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) (gs@rest))#es) LPIVar)
    \<in> lp_cut_mgu_source P"
proof -
  have mgu: "lpc_mgu_unify (lp_ieval a LPIVar) (lp_ieval b LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) (gs@rest))
    (\<lambda>x. lp_ieval (lpc_mgu_substitution V images x) LPIVar)"
    by (rule lpc_checked_mgu_unify[OF checked])
  show ?thesis
    using lp_cut_mgu_source.unify[OF mgu, of "lp_cut_state_eval es LPIVar"]
    by (simp add: lp_cut_state_map_def map_map o_def lp_cut_map_comp
      lp_ieval_finite_subst lp_ieval_subst)
qed

lemma lpc_checked_resolve_retains_continuation:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_resolve fuel P a gs c m es k V images successor"
    and fresh_rest: "lp_cut_short_goals k rest"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a # gs @ rest) c m#es) LPIVar,
    lp_cut_state_eval
      (LPCGoals
        (map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. lpc_mgu_substitution V images (lp_prefix k x)))) (snd (P!c)) @
         map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) (gs@rest))#es) LPIVar)
    \<in> lp_cut_mgu_source P"
proof -
  have enlarged: "lpc_no_resolve fuel P a (gs@rest) c m es k V images
      (LPCGoals
        (map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>x. lpc_mgu_substitution V images (lp_prefix k x)))) (snd (P!c)) @
         map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) (gs@rest))#es)"
    using checked fresh_rest
    by (auto simp: lpc_no_resolve_def lp_cut_short_goals_def list_all_iff)
  show ?thesis by (rule lpc_no_resolve_sound[OF enlarged])
qed

lemma lpc_checked_resolve_swap_retains_continuation:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_no_resolve_swap fuel P a gs c m es k V images x y successor"
    and fresh_rest: "lp_cut_short_goals k rest"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a # gs @ rest) c m#es) LPIVar,
    lp_cut_state_eval
      (LPCGoals
        (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. lpc_mgu_substitution V images (lp_prefix k v)))\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (snd (P!c)) @
         map (lp_cut_map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (gs@rest))#es) LPIVar)
    \<in> lp_cut_mgu_source P"
proof -
  have enlarged: "lpc_no_resolve_swap fuel P a (gs@rest) c m es k V images x y
      (LPCGoals
        (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. lpc_mgu_substitution V images (lp_prefix k v)))\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (snd (P!c)) @
         map (lp_cut_map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (gs@rest))#es)"
    using checked fresh_rest
    by (auto simp: lpc_no_resolve_swap_def lp_cut_short_goals_def list_all_iff)
  show ?thesis by (rule lpc_no_resolve_swap_sound[OF enlarged])
qed

lemma lpc_fresh_resolve_swap_retains_continuation:
  fixes P :: "('f,string) lp_cut_program"
    and rename_clause_var :: "string \<Rightarrow> string"
  assumes index: "c<length P"
    and checked: "lpc_check_mgu fuel
      [(a,fst (P!c)\<cdot>(\<lambda>v. Var (rename_clause_var v)))] V images"
    and injective: "inj rename_clause_var"
    and fresh_a: "vars_term a \<inter> range rename_clause_var = {}"
    and fresh_goals: "\<forall>g\<in>set (gs@rest). \<forall>t\<in>set (lp_cut_terms g).
      vars_term t \<inter> range rename_clause_var = {}"
  shows "(lp_cut_state_eval (LPCClause (LPCAtom a # gs @ rest) c m#es) LPIVar,
    lp_cut_state_eval
      (LPCGoals
        (map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. lpc_mgu_substitution V images (rename_clause_var v)))\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (snd (P!c)) @
         map (lp_cut_map (\<lambda>t. (t\<cdot>lpc_mgu_substitution V images)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (gs@rest))#es) LPIVar)
    \<in> lp_cut_mgu_source P"
proof -
  have mgu: "lpc_mgu_resolve (lp_ieval a LPIVar)
    (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) (gs@rest))
    (fst (P!c)) (snd (P!c))
    (\<lambda>v. lp_ieval (lpc_mgu_substitution V images v) LPIVar)
    (\<lambda>v. lp_ieval (lpc_mgu_substitution V images (rename_clause_var v)) LPIVar)"
    by (rule lpc_checked_mgu_resolve_fresh_namespace[OF checked injective fresh_a fresh_goals])
  show ?thesis
    using lp_cut_mgu_source.resolve[OF index lpc_mgu_resolve_output_swap[OF mgu, of x y],
      of m "lp_cut_state_eval es LPIVar"]
    by (simp add: lp_cut_state_map_def map_map o_def
      lp_cut_map_comp lp_ieval_finite_subst lp_ieval_subst lp_cut_map_bind)
qed

ML \<open>
val checked = [@{thm lpc_prefix_mgu_cannot_instantiate_live_continuation},
 @{thm lpc_checked_unify_retains_continuation},
 @{thm lpc_checked_resolve_retains_continuation},
 @{thm lpc_checked_resolve_swap_retains_continuation},
 @{thm lpc_fresh_resolve_swap_retains_continuation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted continuation-step dependency" else ();
\<close>
end
