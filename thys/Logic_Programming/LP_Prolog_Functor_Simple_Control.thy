theory LP_Prolog_Functor_Simple_Control
 imports LP_Prolog_Finite_Functor_Normalization
begin

text \<open>Case allocation and administrative operations need no unification
  premise. The syntactic check excludes resolution, equality and meta-call
  expansion; these retain their separate finite-execution obligations.\<close>

fun lpp_simple_control_frame where
 "lpp_simple_control_frame ((LPCClause gs c m,a)#ss) = False"
| "lpp_simple_control_frame ((LPCGoals (LPCUnify x y#gs),a)#ss) = False"
| "lpp_simple_control_frame ((LPCGoals (LPCMeta x#gs),a)#ss) = False"
| "lpp_simple_control_frame ss = True"

lemma lpp_simple_control_frame_eval:
 "lpp_simple_control_frame (lpc_return_eval eta ss) = lpp_simple_control_frame ss"
 by (induct ss rule: lpp_simple_control_frame.induct)
   (simp_all add: lpc_return_eval_def)

lemma lpp_finite_simple_base_step:
 assumes simple: "lpp_simple_control_frame ss"
 and step: "lpc_answer_transition P ss event tt"
 and finite: "lpp_finite_execution ss"
 shows "lpp_finite_execution tt"
 by (rule lpp_finite_base_answer_step[OF step finite]) (use simple in auto)

lemma lpp_finite_simple_domain_step:
 assumes simple: "lpp_simple_control_frame ss"
 and clear: "lpp_no_builtin_frame ss"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ss) event tt"
 and finite: "lpp_finite_execution (lpc_return_eval eta ss)"
 shows "lpp_finite_execution tt"
proof -
 have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain
   (map fst (lpc_return_eval eta ss))"
  by (rule lpp_no_builtin_domain_bad[OF lpp_no_builtin_frame_sound[OF clear]])
 have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
   (lpc_return_eval eta ss) event tt"
  using step supported by (simp add: lpp_domain_answers_def)
 have base: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  by (rule lpp_univ_source_nonbuiltin_base[OF clear actual])
 show ?thesis by (rule lpp_finite_simple_base_step[OF _ base finite])
  (simp add: lpp_simple_control_frame_eval simple)
qed

lemma lpp_finite_functor_simple_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and simple: "lpp_simple_control_frame (states!i)"
 and clear: "lpp_no_builtin_frame (states!i)"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
 by (rule lpp_functor_cut_node_contract[OF compatible transfer checked])
   (rule lpp_finite_simple_domain_step[OF simple clear]; assumption)

lemma lpp_finite_functor_test_step:
 assumes name: "lpp_var_name f"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)) event tt"
 and finite: "lpp_finite_execution (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved))"
 shows "lpp_finite_execution tt"
 using step finite
 by (auto simp: lpp_domain_answers_def lpc_return_eval_def lpp_univ_term_test_step[OF name]
   lpp_finite_execution_def lpp_finite_goals_def split: if_splits)

lemma lpp_finite_functor_test_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "states!i=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"
 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   lpp_finite_execution returned arity i"
proof -
 have name: "lpp_var_name f"
  using checked by (auto simp: shape lpp_check_functor_source_action_def lpp_check_functor_term_test_def)
 show ?thesis by (rule lpp_functor_test_node_contract[OF compatible transfer checked shape])
  (simp only: shape; rule lpp_finite_functor_test_step[OF name]; assumption)
qed

lemma lpp_simple_control_resolution_rejected:
 "\<not> lpp_simple_control_frame ((LPCClause (LPCAtom a#gs) c m,eta)#saved)"
 by simp

lemma lpp_simple_control_equality_rejected:
 "\<not> lpp_simple_control_frame ((LPCGoals (LPCUnify a b#gs),eta)#saved)"
 by simp

lemma lpp_simple_control_meta_rejected:
 "\<not> lpp_simple_control_frame ((LPCGoals (LPCMeta a#gs),eta)#saved)"
 by simp

ML \<open>
val checked = @{thms lpp_finite_functor_test_step lpp_finite_functor_test_node_contract lpp_simple_control_frame_eval lpp_finite_simple_base_step lpp_finite_simple_domain_step
 lpp_finite_functor_simple_node_contract lpp_simple_control_resolution_rejected
 lpp_simple_control_equality_rejected lpp_simple_control_meta_rejected};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted simple functor control dependency" else ();
\<close>
end
