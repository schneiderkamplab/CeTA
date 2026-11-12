theory LP_Prolog_NO_Renamed_Trace
 imports LP_Prolog_NO_Renamed_Machine
begin

fun lpp_no_return_step_support where
 "lpp_no_return_step_support P ss (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary action)))) =
   lpc_no_action_support P action"
| "lpp_no_return_step_support P ss (LPPMIs e) = lpp_no_return_is_support ss"
| "lpp_no_return_step_support P ss action = {}"

lemma lpp_no_return_step_support_finite[simp]:
 "finite (lpp_no_return_step_support P ss action)"
 by (induct P ss action rule: lpp_no_return_step_support.induct) simp_all

fun lpp_no_action_scope_safe where
 "lpp_no_action_scope_safe rest (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary action)))) =
   lpc_no_action_scope_safe rest action"
| "lpp_no_action_scope_safe rest (LPPMProbe m n) =
   (m\<notin>lpc_rest_scopes rest \<and> n\<notin>lpc_rest_scopes rest)"
| "lpp_no_action_scope_safe rest action = True"

lemma lpp_no_return_step_renamed_sound:
 assumes checked: "lpp_no_return_step fuel P reserved ss action tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_step_support P ss action = {}"
   and scopes: "lpp_no_action_scope_safe rest action"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 using checked safe scopes
 by (induct fuel P reserved ss action tt rule: lpp_no_return_step.induct)
   (auto simp: lpc_no_return_rename_safe_def
     intro: lpp_no_return_ordinary_renamed_sound[OF _ inverse]
       lpp_no_return_is_renamed_sound[OF _ inverse]
       lpp_no_return_compare_sound[OF lpp_no_return_compare_renamed]
       lpp_no_return_integer_sound[OF lpp_no_return_integer_renamed]
       lpp_no_return_probe_renamed_sound
       lpp_no_return_list_sound[OF lpp_no_return_list_renamed])

fun lpp_no_return_trace_support where
 "lpp_no_return_trace_support P ss [] = {}"
| "lpp_no_return_trace_support P ss ((action,uu)#steps) =
   lpp_no_return_step_support P ss action \<union> lpp_no_return_trace_support P uu steps"

lemma lpp_no_return_trace_support_finite[simp]:
 "finite (lpp_no_return_trace_support P ss steps)"
 by (induct steps arbitrary: ss) (auto split: prod.splits)

lemma lpp_no_return_trace_renamed_sound:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked safe scopes
proof (induct steps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons entry steps)
 obtain action uu where entry: "entry=(action,uu)" by (cases entry) auto
 have local_step: "lpp_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpp_no_return_trace fuel P reserved uu steps tt"
   and local_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_step_support P ss action = {}"
   and tail_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P uu steps = {}"
   and local_scopes: "lpp_no_action_scope_safe rest action"
   and tail_scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
   using Cons.prems entry by auto
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_no_return_step_renamed_sound[OF local_step inverse local_safe local_scopes])
 show ?case using actual Cons.hyps[OF local_tail tail_safe tail_scopes]
   by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpp_no_return_trace_renamed_progress:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
   and nonempty: "steps\<noteq>[]"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain action uu tail where shape: "steps=(action,uu)#tail" using nonempty by (cases steps) auto
 have local_step: "lpp_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpp_no_return_trace fuel P reserved uu tail tt"
   and local_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_step_support P ss action = {}"
   and tail_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P uu tail = {}"
   and local_scopes: "lpp_no_action_scope_safe rest action"
   and tail_scopes: "\<forall>action\<in>set (map fst tail). lpp_no_action_scope_safe rest action"
   using checked safe scopes shape by auto
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_no_return_step_renamed_sound[OF local_step inverse local_safe local_scopes])
 show ?thesis using actual lpp_no_return_trace_renamed_sound[OF local_tail inverse tail_safe tail_scopes]
   by (rule rtrancl_into_trancl2)
qed

lemma lpp_no_return_trace_fresh_progress:
 fixes A C :: "string set"
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and finite: "finite A" "finite C"
   and separate: "A \<inter> C = {}"
   and caller: "(\<Union>t\<in>set extra. vars_term t) \<subseteq> C"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
   and nonempty: "steps\<noteq>[]"
 shows "\<exists>p. (\<forall>z. p (p z) = z) \<and> (\<forall>z\<in>A. p z = z) \<and>
   (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
    lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain p where inverse: "\<forall>z. p (p z) = z" and fixed: "\<forall>z\<in>A. p z = z"
   and disjoint: "C \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   using lpc_no_fresh_finite_support[OF finite(1) lpp_no_return_trace_support_finite[of P ss steps] finite(2) separate]
   by (elim exE conjE) assumption
 have safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   using disjoint caller by auto
 have path: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
    lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   by (rule lpp_no_return_trace_renamed_progress[OF checked _ safe scopes nonempty]) (use inverse in auto)
 show ?thesis
 proof (rule exI[of _ p], intro conjI)
   show "\<forall>z. p (p z) = z" by (rule inverse)
   show "\<forall>z\<in>A. p z = z" by (rule fixed)
   show "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
    lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
     by (rule path)
 qed
qed

ML \<open>
val checked = [@{thm lpp_no_return_step_renamed_sound}, @{thm lpp_no_return_trace_support_finite},
 @{thm lpp_no_return_trace_fresh_progress}, @{thm lpp_no_return_trace_renamed_sound}, @{thm lpp_no_return_trace_renamed_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted uniformly renamed Prolog trace" else ();
\<close>
end
