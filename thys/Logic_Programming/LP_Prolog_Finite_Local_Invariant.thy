theory LP_Prolog_Finite_Local_Invariant
 imports LP_Prolog_Finite_Local_State
begin

fun lpp_check_static_resolution_entry where
 "lpp_check_static_resolution_entry A P (LPCClause gs c m) =
   (c<length P \<longrightarrow> list_all (lpp_static_template A) (snd (P!c)))"
| "lpp_check_static_resolution_entry A P e = True"

fun lpp_check_static_resolution_state where
 "lpp_check_static_resolution_state A P [] = True"
| "lpp_check_static_resolution_state A P ((e,active)#saved) = lpp_check_static_resolution_entry A P e"

lemma lpp_local_static_ordinary_step:
 assumes checked: "lpp_check_static_resolution_state A P ss"
   and transition: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
   and state: "lpp_static_state A (map fst (lpc_return_eval eta ss))"
 shows "lpp_static_state A (map fst tt)"
 using transition state
proof (cases rule: lpc_answer_transition.cases)
 case (resolve c a gs sigma rho m env es)
 obtain e active saved where source: "ss=(e,active)#saved"
   and shape: "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e=LPCClause (LPCAtom a#gs) c m"
   using resolve by (cases ss; auto simp: lpc_return_eval_def split: prod.splits)
 have body: "list_all (lpp_static_template A) (snd (P!c))"
   using checked shape resolve by (cases e; auto simp: source)
 show ?thesis using resolve state body
   by (auto simp: lpp_static_state_def list_all_iff intro: lpp_static_evaluate lpp_static_substitute)
next
 case (cut m gs env es)
 have static: "lpp_static_state A (map fst es)"
   using state cut by (auto simp: lpp_static_state_def)
 have pruned: "lpp_static_state A (lp_cut_prune m (map fst es))"
   by (rule lpp_static_prune[OF static])
 show ?thesis using state cut pruned
   by (auto simp: lpp_static_state_def lpc_answer_prune_erases)
qed (auto simp: lpp_static_state_def list_all_iff lpc_answer_prune_erases
  intro: lpp_static_substitute)

lemma lpp_local_invariant_ordinary_step:
 assumes finite_check: "lpp_check_finite_resolution_state G P ss"
   and static_check: "lpp_check_static_resolution_state A P ss"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and transition: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
   and state: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
 shows "lpp_finite_direct_invariant A tt"
 using state lpp_finite_local_ordinary_step[OF finite_check known transition]
   lpp_local_static_ordinary_step[OF static_check transition]
 by (auto simp: lpp_finite_direct_invariant_def)

lemma lpp_local_invariant_answer_step:
 assumes finite_check: "lpp_check_finite_resolution_state G P ss"
   and static_check: "lpp_check_static_resolution_state A P ss"
   and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   and safe: "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow>
     U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   and step: "lpp_answer_transition P B U (lpc_return_eval eta ss) event tt"
   and state: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
 shows "lpp_finite_direct_invariant A tt"
 using step state
proof (cases rule: lpp_answer_transition.cases)
 case base
 show ?thesis
   by (rule lpp_local_invariant_ordinary_step[OF finite_check static_check, where eta=eta])
      (use base state known in auto)
qed (auto simp: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
      lpp_static_state_def list_all_iff
    dest: safe intro: lpp_finite_direct_substitute lpp_static_substitute)

lemma lpp_local_invariant_domain_step:
 assumes "lpp_check_finite_resolution_state G P ss"
   "lpp_check_static_resolution_state A P ss"
   "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
   "\<And>f ts result. (f,length ts)\<in>A \<Longrightarrow> U f ts result \<Longrightarrow> lpp_finite_direct_outcome result"
   "lpp_domain_answers P B U D (lpc_return_eval eta ss) event tt"
   "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
 shows "lpp_finite_direct_invariant A tt"
 using assms(5,6) lpp_local_invariant_answer_step[where eta=eta, OF assms(1,2,3,4)]
 by (auto simp: lpp_domain_answers_def)

ML \<open>
val checked = [@{thm lpp_local_invariant_domain_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted local invariant transport" else ();
\<close>
end
