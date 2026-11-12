theory LP_Cut_NO_Finite_Attachment
 imports LP_Prolog_NO_Renamed_Trace LP_Cut_NO_Context_Template
begin

text \<open>Finite answer rows and finite caller templates reconstruct a finite
source state. This is representation, not a finite-tree assumption about all
Prolog executions: evaluation under a general environment may still be rational.\<close>

definition lpc_no_return_finite_env :: "('f lp_cut_symbol,'v) term list \<Rightarrow> nat \<Rightarrow> ('f lp_cut_symbol,'v) term" where
 "lpc_no_return_finite_env payload n = (if n<length payload then payload!n else Fun LPCTruth [])"

lemma lpc_no_return_finite_eval:
 "lp_ieval (t\<cdot>lpc_no_return_finite_env payload) eta = lp_ieval t (lpc_return_env payload eta)"
proof -
 have env: "(\<lambda>x. lp_ieval (lpc_no_return_finite_env payload x) eta) = lpc_return_env payload eta"
   by (rule ext) (simp add: lpc_no_return_finite_env_def lpc_return_env_def)
 show ?thesis by (simp only: lp_ieval_finite_subst env)
qed

fun lpc_no_attach_finite_frame where
 "lpc_no_attach_finite_frame rest (LPCGoals gs,payload) =
   LPCGoals (gs @ map (lp_cut_map (\<lambda>t. t\<cdot>lpc_no_return_finite_env payload)) rest)"
| "lpc_no_attach_finite_frame rest (LPCClause gs c m,payload) =
   LPCClause (gs @ map (lp_cut_map (\<lambda>t. t\<cdot>lpc_no_return_finite_env payload)) rest) c m"
| "lpc_no_attach_finite_frame rest (LPCBarrier m,payload) = LPCBarrier m"

definition lpc_no_attach_finite where
 "lpc_no_attach_finite rest ss = map (lpc_no_attach_finite_frame rest) ss"

lemma lpc_no_attach_finite_frame_eval:
 "lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (lpc_no_attach_finite_frame rest (e,payload)) =
   lpc_attach_frame rest (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,lpc_return_env payload eta)"
 by (cases e) (simp_all add: map_map o_def lp_cut_map_comp lpc_no_return_finite_eval)

lemma lpc_no_attach_finite_eval:
 "lp_cut_state_eval (lpc_no_attach_finite rest ss) eta = lpc_attach rest (lpc_return_eval eta ss)"
 by (induct ss) (auto simp: lpc_no_attach_finite_def lp_cut_state_map_def lpc_return_eval_def
   lpc_no_attach_finite_frame_eval split: prod.splits)

lemma lpc_no_attach_finite_selected_call:
 "lpc_no_attach_finite rest ((LPCGoals (LPCAtom a#gs),payload)#saved) =
   LPCGoals (LPCAtom a#gs @ map (lp_cut_map (\<lambda>t. t\<cdot>lpc_no_return_finite_env payload)) rest)#
     lpc_no_attach_finite rest saved"
 by (simp add: lpc_no_attach_finite_def)

lemma lpc_no_fixed_term_rename:
 assumes fixed: "\<forall>x\<in>vars_term t. p x = x"
 shows "t\<cdot>(Var \<circ> p) = t"
 by (rule subst_apply_term_ident) (use fixed in \<open>auto simp: subst_domain_def o_def\<close>)

ML \<open>
val checked = [@{thm lpc_no_return_finite_eval}, @{thm lpc_no_attach_finite_eval},
 @{thm lpc_no_attach_finite_selected_call}, @{thm lpc_no_fixed_term_rename}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite caller reconstruction" else ();
\<close>
end
