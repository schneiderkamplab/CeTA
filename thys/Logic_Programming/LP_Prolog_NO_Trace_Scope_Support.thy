theory LP_Prolog_NO_Trace_Scope_Support
 imports LP_Prolog_NO_Owned_Return_Trace
begin

fun lpc_no_action_scope_support where
 "lpc_no_action_scope_support (LPCNOCase m) = {m}"
| "lpc_no_action_scope_support action = {}"

fun lpp_no_action_scope_support where
 "lpp_no_action_scope_support (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary action)))) =
   lpc_no_action_scope_support action"
| "lpp_no_action_scope_support action = {}"

lemma lpc_no_action_scopes_safe:
 "lpc_no_action_scope_safe rest action =
   (lpc_no_action_scope_support action \<inter> lpc_rest_scopes rest = {})"
 by (cases action) simp_all

lemma lpp_no_action_scopes_safe:
 "lpp_no_action_scope_safe rest action =
   (lpp_no_action_scope_support action \<inter> lpc_rest_scopes rest = {})"
 by (induct rest action rule: lpp_no_action_scope_safe.induct)
   (simp_all add: lpc_no_action_scopes_safe)

lemma lpc_no_action_scope_support_finite[simp]:
 "finite (lpc_no_action_scope_support action)"
 by (cases action) simp_all

lemma lpp_no_action_scope_support_finite[simp]:
 "finite (lpp_no_action_scope_support action)"
 by (induct action rule: lpp_no_action_scope_support.induct) simp_all

definition lpp_no_trace_scope_support where
 "lpp_no_trace_scope_support steps =
  (\<Union>uu\<in>set (map snd steps). lpc_no_rows_scopes uu) \<union>
  (\<Union>action\<in>set (map fst steps). lpp_no_action_scope_support action)"

lemma lpc_no_rows_scopes_finite[simp]:
 "finite (lpc_no_rows_scopes ss)"
 unfolding lpc_no_rows_scopes_def by (rule lpc_no_scopes_finite)

lemma lpp_no_trace_scope_support_finite[simp]:
 "finite (lpp_no_trace_scope_support steps)"
 by (auto simp: lpp_no_trace_scope_support_def)

lemma lpp_no_trace_scope_support_targets:
 "\<forall>uu\<in>set (map snd steps). lpc_no_rows_scopes uu \<subseteq> lpp_no_trace_scope_support steps"
 by (auto simp: lpp_no_trace_scope_support_def)

lemma lpp_no_trace_scope_preimage_safe:
 assumes inverse: "\<forall>x. r (r x) = x"
   and separated: "r ` lpp_no_trace_scope_support steps \<inter> lpc_rest_scopes rest = {}"
 shows "\<forall>action\<in>set (map fst steps).
   lpp_no_action_scope_safe (map (lp_cut_scope_goal r) rest) action"
proof -
 have preimage: "lpp_no_trace_scope_support steps \<inter> r ` lpc_rest_scopes rest = {}"
   by (rule lpc_no_scope_preimage_separate[OF inverse separated])
 show ?thesis using preimage
   by (auto simp: lpp_no_action_scopes_safe lpp_no_trace_scope_support_def lp_cut_scope_goal_scopes)
qed

ML \<open>
val checked = [@{thm lpp_no_action_scopes_safe}, @{thm lpp_no_trace_scope_support_finite},
 @{thm lpp_no_trace_scope_support_targets}, @{thm lpp_no_trace_scope_preimage_safe}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted trace scope support" else ();
\<close>
end
