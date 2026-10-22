theory LP_Cut_Failure
  imports LP_Cut_State
begin

lemma lp_cut_source_clause_failure:
  fixes a :: "('f lp_cut_symbol,'w) lp_iterm"
  assumes step: "(LPCClause (LPCAtom a#gs) c m#es,t)\<in>lp_cut_source P"
    and impossible: "\<not>(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm.
      \<exists>\<rho>. lp_isubst a \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
  shows "t=es"
  using step impossible by (cases rule: lp_cut_source.cases) auto

lemma lp_cut_source_equality_failure:
  fixes a :: "('f lp_cut_symbol,'w) lp_iterm"
  assumes step: "(LPCGoals (LPCUnify a b#gs)#es,t)\<in>lp_cut_source P"
    and impossible: "\<not>(\<exists>\<sigma>::'w\<Rightarrow>('f lp_cut_symbol,'w) lp_iterm.
      lp_isubst a \<sigma> = lp_isubst b \<sigma>)"
  shows "t=es"
  using step impossible by (cases rule: lp_cut_source.cases) auto

fun lp_cut_failure_next where
  "lp_cut_failure_next P fuel k (LPCClause (LPCAtom a#gs) c m#es) =
    (if c<length P \<and> lp_cut_check_clash fuel k a (fst (P!c)) then Some es else None)"
| "lp_cut_failure_next P fuel k (LPCGoals (LPCUnify a b#gs)#es) =
    (if lp_cut_check_equality fuel a b LPCAlwaysFailure then Some es else None)"
| "lp_cut_failure_next P fuel k _ = None"

theorem lp_cut_checked_failure_covers:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_cut_failure_next P fuel k s=Some t"
    and step: "(lp_cut_state_eval s \<eta>,u)\<in>lp_cut_source P"
  shows "u=lp_cut_state_eval t \<eta>"
  using checked step
proof (induct P fuel k s arbitrary: t rule: lp_cut_failure_next.induct)
  case (1 P fuel k a gs c m es)
  have clash: "lp_cut_check_clash fuel k a (fst (P!c))" and tail: "t=es"
    using "1.prems"(1) by (auto split: if_splits)
  have impossible: "\<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm. \<exists>\<rho>.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_ieval (fst (P!c)) \<rho>)"
    by (rule lp_cut_check_clash_sound[OF clash])
  show ?case
    using lp_cut_source_clause_failure[OF _ impossible] "1.prems"(2) tail
    by (simp add: lp_cut_state_map_def)
next
  case (2 P fuel k a b gs es)
  have clash: "lp_cut_check_equality fuel a b LPCAlwaysFailure" and tail: "t=es"
    using "2.prems"(1) by (auto split: if_splits)
  have impossible: "\<not>(\<exists>\<sigma>::string\<Rightarrow>('f lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval a \<eta>) \<sigma> = lp_isubst (lp_ieval b \<eta>) \<sigma>)"
    by (rule lp_cut_equality_failure[OF clash])
  show ?case
    using lp_cut_source_equality_failure[OF _ impossible] "2.prems"(2) tail
    by (simp add: lp_cut_state_map_def)
qed simp_all

text \<open>No local search failure can be used as this certificate: the
checker itself must establish a clash for every represented runtime valuation.\<close>

end
