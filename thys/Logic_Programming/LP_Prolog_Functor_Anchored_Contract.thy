theory LP_Prolog_Functor_Anchored_Contract
 imports LP_Prolog_Functor_Finite_Unification
begin

text \<open>Repeated head variables are safe when all their runtime images are
  anchored by checked ground inputs. Groundness can come from an incoming
  return context; it does not imply integer typing.\<close>

lemma lpp_finite_anchored_resolution_base_step:
 assumes step: "lpc_answer_transition P
   ((LPCClause (LPCAtom (lp_ieval (Fun f actuals) eta)#gs) c m,ret)#saved) event tt"
 and finite: "lpp_finite_execution
   ((LPCClause (LPCAtom (lp_ieval (Fun f actuals) eta)#gs) c m,ret)#saved)"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and checked: "lpp_check_anchored_head G actuals hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 shows "lpp_finite_execution tt"
proof (rule lpp_finite_base_answer_step[OF step finite])
 fix a' gs' c' m' eta' es sigma rho
 assume shape: "((LPCClause (LPCAtom (lp_ieval (Fun f actuals) eta)#gs) c m,ret)#saved)=
   (LPCClause (LPCAtom a'#gs') c' m',eta')#es"
 and bound: "c'<length P"
 and mgu: "lpc_mgu_resolve a' gs' (fst (P!c')) (snd (P!c')) sigma rho"
 have equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals=map (\<lambda>t. lp_ieval t rho) hs"
  using mgu shape head by (auto simp: lpc_mgu_resolve_def map_map o_def)
 have ground_head: "lp_seg_ground (lp_ieval (Fun f hs) rho)"
  by (rule lpp_checked_anchored_head_ground[OF checked lengths known equation])
 show "lpp_finite_term (lp_ieval (fst (P!c')) rho)"
  using lpp_ground_finite_term[OF ground_head] shape head by simp
qed auto

lemma lpp_finite_functor_anchored_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and shape: "states!i=((LPCClause (LPCAtom (Fun f actuals)#gs) c m,active)#saved)"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
proof (rule lpp_functor_contextual_cut_node_contract[OF compatible transfer checked])
 fix eta ev ys
 assume known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have runtime_ground: "lp_seg_ground (eta x)" if "x\<in>set G" for x
  using ground known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 have clear: "lpp_no_builtin_frame (states!i)" by (simp add: shape)
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta (states!i)))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta (states!i)) ev ys"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show "lpp_finite_execution ys"
  using lpp_finite_anchored_resolution_base_step[OF _ _ head lengths anchored runtime_ground] base finite
  by (simp add: shape lpc_return_eval_def)
qed

lemma lpp_anchored_repeated_head_positive:
 "lpp_check_anchored_head [''counter'']
   [Fun f [],Var ''counter'',Var ''out''] [Fun f [],Var ''shared'',Var ''shared'']"
 by (simp add: lpp_check_anchored_head_def)

lemma lpp_anchored_repeated_head_missing_ground_rejected:
 "\<not>lpp_check_anchored_head []
   [Fun f [],Var ''counter'',Var ''out''] [Fun f [],Var ''shared'',Var ''shared'']"
 by (simp add: lpp_check_anchored_head_def)

ML \<open>
val checked = @{thms lpp_finite_anchored_resolution_base_step lpp_finite_functor_anchored_node_contract
 lpp_anchored_repeated_head_positive lpp_anchored_repeated_head_missing_ground_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted anchored functor contract dependency" else ();
\<close>
end
