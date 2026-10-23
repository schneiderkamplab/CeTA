theory LP_Cut_Answer_Control
  imports LP_Cut_Answers LP_Cut_Control_Residual
begin

text \<open>Cut erasure is used here ONLY to overapproximate successful answers.
It is not used to infer termination of the erased program, or nontermination of
the source. A cut may remove answers, but every retained answer must still obey
the cut-free answer contract. Unsupported meta/equality goals are excluded by
the existing executable control-program condition.\<close>

lemma lpc_control_answer_resolution:
  fixes P :: "('f,string) lp_cut_program"
    and \<eta> :: "'v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lpc_control_program P Q F"
    and f: "f\<in>F" and tail: "list_all (lpc_control_igoal F) gs"
    and c: "c<length P" and eq: "lp_isubst (LPIFun (LPCUser f) ts) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
  shows "(( (LPCUser f,ts)#map lpc_control_iatom gs,\<eta>),
    (map lpc_control_iatom (map (lp_cut_bind m (\<lambda>t. lp_ieval t \<rho>)) (snd (P!c)) @
       map (lp_cut_map (\<lambda>t. lp_isubst t \<sigma>)) gs),
       \<lambda>x. lp_isubst (\<eta> x) \<sigma>))\<in>lp_seg_answer_step Q"
proof -
  obtain g us where h: "fst (P!c)=Fun g us"
    and selected: "\<And>f. g=LPCUser f \<Longrightarrow> f\<in>F \<Longrightarrow>
      list_all (lpc_control_goal F) (snd (P!c)) \<and>
      ((LPCUser f,us),map lpc_control_atom (snd (P!c)))\<in>set Q"
    using program c unfolding lpc_control_program_def by blast
  have gf: "g=LPCUser f" using eq by (simp add: h)
  have body: "list_all (lpc_control_goal F) (snd (P!c))"
    and clause: "((LPCUser f,us),map lpc_control_atom (snd (P!c)))\<in>set Q"
    using selected f gf by auto
  obtain i where i: "i<length Q" and qi:
    "Q!i=((LPCUser f,us),map lpc_control_atom (snd (P!c)))"
    using clause by (auto simp: in_set_conv_nth)
  have unifies: "lp_iatom_subst (LPCUser f,ts) \<sigma> = lp_atom_eval (fst (Q!i)) \<rho>"
    using eq by (simp add: h gf qi lp_iatom_subst_def lp_atom_eval_def)
  note st = lp_seg_answer_step.resolve[OF i unifies, where gs="map lpc_control_iatom gs" and \<rho>=\<eta>]
  show ?thesis using st
    by (simp only: qi fst_conv snd_conv map_append
      lpc_control_bind(2)[OF body] lpc_control_subst(2)[OF tail])
qed

fun lpc_control_answer_frame where
  "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>) =
    (list_all (lpc_control_igoal F) gs \<and>
     ((origin,\<eta>),(map lpc_control_iatom gs,\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*)"
| "lpc_control_answer_frame Q F origin \<eta> (LPCClause gs c m,\<rho>) =
    (list_all (lpc_control_igoal F) gs \<and>
     ((origin,\<eta>),(map lpc_control_iatom gs,\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*)"
| "lpc_control_answer_frame Q F origin \<eta> (LPCBarrier m,\<rho>) = True"

lemma lpc_answer_prune_subset:
  "set (lpc_answer_prune m ss) \<subseteq> set ss"
  by (induct ss) (auto split: prod.splits lp_cut_entry.splits if_splits)

lemma lpc_control_answer_truth:
  fixes P :: "('f,string) lp_cut_program"
    and gs :: "('f lp_cut_symbol,string) lp_iatom list"
    and \<eta> :: "'v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lpc_control_program P Q F"
  shows "(((LPCTruth,[])#gs,\<eta>),(gs,\<eta>))\<in>lp_seg_answer_step Q"
proof -
  obtain i where i: "i<length Q" and qi: "Q!i=((LPCTruth,[]),[])"
    using program by (auto simp: lpc_control_program_def in_set_conv_nth)
  have eq: "lp_iatom_subst (LPCTruth,[]) (LPIVar :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) = lp_atom_eval (fst (Q!i)) LPIVar"
    by (simp add: qi lp_iatom_subst_def lp_atom_eval_def)
  show ?thesis using lp_seg_answer_step.resolve[OF i eq, where gs=gs and \<rho>=\<eta>] by (simp add: qi)
qed

lemma lpc_control_answer_drop:
  fixes P :: "('f,string) lp_cut_program"
    and \<rho> :: "'v \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes program: "lpc_control_program P Q F"
    and known: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals (g#gs),\<rho>)"
    and truth: "lpc_control_iatom g=(LPCTruth,[])"
  shows "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>)"
proof -
  have before: "((origin,\<eta>),((LPCTruth,[])#map lpc_control_iatom gs,\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
    using known truth by simp
  have after: "(((LPCTruth,[])#map lpc_control_iatom gs,\<rho>),(map lpc_control_iatom gs,\<rho>))\<in>lp_seg_answer_step Q"
    by (rule lpc_control_answer_truth[OF program])
  show ?thesis using rtrancl_into_rtrancl[OF before after] known by simp
qed

theorem lpc_control_answers_preserved:
  assumes program: "lpc_control_program P Q F"
    and step: "lpc_answer_transition P ss event tt"
    and known: "list_all (lpc_control_answer_frame Q F origin \<eta>) ss"
  shows "list_all (lpc_control_answer_frame Q F origin \<eta>) tt"
  using step known
proof (cases rule: lpc_answer_transition.cases)
  case (truth gs \<rho> es)
  have old: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals (LPCTrue#gs),\<rho>)"
    using known truth by simp
  have continued: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>)"
    by (rule lpc_control_answer_drop[OF program old]) simp
  show ?thesis using continued known truth by simp
next
  case (cut m gs \<rho> es)
  have old: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals (LPCCut m#gs),\<rho>)"
    using known cut by simp
  have continued: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>)"
    by (rule lpc_control_answer_drop[OF program old]) simp
  show ?thesis using continued known cut lpc_answer_prune_subset[of m es]
    by (auto simp: list_all_iff)
next
  case (resolve c a gs \<sigma> \<rho> m \<nu> es)
  obtain f ts where a: "a=LPIFun (LPCUser f) ts" and f: "f\<in>F"
    and tail: "list_all (lpc_control_igoal F) gs"
    and before: "((origin,\<eta>),((LPCUser f,ts)#map lpc_control_iatom gs,\<nu>))\<in>(lp_seg_answer_step Q)\<^sup>*"
    using known resolve by (auto simp: lpc_control_igoal_iff)
  have eq: "lp_isubst (LPIFun (LPCUser f) ts) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
    using resolve a by (simp add: lpc_mgu_resolve_def)
  have c: "c<length P" using resolve by simp
  note domain = lpc_control_resolution(1)[OF program f tail c eq, of m]
  note ast = lpc_control_answer_resolution[OF program f tail c eq, of \<nu> m]
  note path = rtrancl_into_rtrancl[OF before ast]
  show ?thesis using known resolve domain path by simp
qed (auto simp: list_all_iff lpc_control_igoal_iff)

lemma lpc_control_answer_trace_invariant:
  assumes program: "lpc_control_program P Q F"
    and path: "(ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
    and known: "list_all (lpc_control_answer_frame Q F origin \<eta>) ss"
  shows "list_all (lpc_control_answer_frame Q F origin \<eta>) tt"
  using path known
proof (induct rule: rtrancl_induct)
  case base then show ?case .
next
  case (step ys zs)
  obtain event where st: "lpc_answer_transition P ys event zs"
    using step.hyps(2) by (auto simp: lpc_answer_steps_def)
  show ?case by (rule lpc_control_answers_preserved[OF program st step.hyps(3)[OF step.prems]])
qed

theorem lpc_control_successful_answer:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P ss (Some \<rho>) tt"
  shows "((map lpc_control_iatom gs,\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
proof -
  have origin: "list_all (lpc_control_answer_frame Q F (map lpc_control_iatom gs) \<eta>)
    [(LPCGoals gs,\<eta>)]" using domain by simp
  note known = lpc_control_answer_trace_invariant[OF program path origin]
  have shape: "ss=(LPCGoals [],\<rho>)#tt" by (rule lpc_answer_event_is_success[OF event])
  show ?thesis using known by (simp add: shape)
qed

corollary lpc_control_answer_contract_transfer:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and contract: "\<And>\<rho>. ((map lpc_control_iatom gs,\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>* \<Longrightarrow> C \<rho>"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P ss (Some \<rho>) tt"
  shows "C \<rho>"
  by (rule contract[OF lpc_control_successful_answer[OF program domain path event]])

corollary lpc_control_answers_keep_ground_inputs:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P ss (Some \<rho>) tt"
    and ground: "lp_seg_ground (\<eta> x)"
  shows "\<rho> x = \<eta> x"
  by (rule lp_seg_answer_steps_preserve_ground[OF
    lpc_control_successful_answer[OF program domain path event] ground])

end
