theory LP_Prolog_NO_Owned_Return_Trace
 imports LP_Prolog_NO_Owned_Return
begin

fun lpp_no_return_boundaries where
 "lpp_no_return_boundaries ss [] = True"
| "lpp_no_return_boundaries ss ((action,tt)#steps) =
   (lpp_no_return_owned_boundary ss tt \<and> lpp_no_return_boundaries tt steps)"

lemma lpp_no_return_trace_owned_sound:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   and boundaries: "lpp_no_return_boundaries ss steps"
   and support: "\<forall>uu\<in>set (map snd steps). lpc_no_rows_scopes uu \<subseteq> S"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_owned_delta_relation P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)) S)\<^sup>*"
 using checked safe scopes boundaries support
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
   and local_boundary: "lpp_no_return_owned_boundary ss uu"
   and tail_boundaries: "lpp_no_return_boundaries uu steps"
   and local_support: "lpc_no_rows_scopes uu \<subseteq> S"
   and tail_support: "\<forall>vv\<in>set (map snd steps). lpc_no_rows_scopes vv \<subseteq> S"
   using Cons.prems entry by auto
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))
   \<in>lpp_owned_delta_relation P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)) S"
   by (rule lpp_no_return_owned_step[OF local_step inverse local_safe local_scopes local_boundary local_support])
 show ?case using actual Cons.hyps[OF local_tail tail_safe tail_scopes tail_boundaries tail_support]
   by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpp_no_return_trace_owned_progress:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   and boundaries: "lpp_no_return_boundaries ss steps"
   and support: "\<forall>uu\<in>set (map snd steps). lpc_no_rows_scopes uu \<subseteq> S"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
   and nonempty: "steps\<noteq>[]"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>(lpp_owned_delta_relation P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)) S)\<^sup>+"
proof -
 obtain action uu tail where shape: "steps=(action,uu)#tail" using nonempty by (cases steps) auto
 have local_step: "lpp_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpp_no_return_trace fuel P reserved uu tail tt"
   and local_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_step_support P ss action = {}"
   and tail_safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P uu tail = {}"
   and local_scopes: "lpp_no_action_scope_safe rest action"
   and tail_scopes: "\<forall>action\<in>set (map fst tail). lpp_no_action_scope_safe rest action"
   and local_boundary: "lpp_no_return_owned_boundary ss uu"
   and tail_boundaries: "lpp_no_return_boundaries uu tail"
   and local_support: "lpc_no_rows_scopes uu \<subseteq> S"
   and tail_support: "\<forall>vv\<in>set (map snd tail). lpc_no_rows_scopes vv \<subseteq> S"
   using checked safe scopes boundaries support shape by auto
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra uu)))
   \<in>lpp_owned_delta_relation P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)) S"
   by (rule lpp_no_return_owned_step[OF local_step inverse local_safe local_scopes local_boundary local_support])
 show ?thesis using actual lpp_no_return_trace_owned_sound[OF local_tail inverse tail_safe tail_boundaries tail_support tail_scopes]
   by (rule rtrancl_into_trancl2)
qed


lemma lpp_no_return_trace_saved_progress:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_trace_support P ss steps = {}"
   and boundaries: "lpp_no_return_boundaries ss steps"
   and support: "\<forall>uu\<in>set (map snd steps). lpc_no_rows_scopes uu \<subseteq> S"
   and scopes: "\<forall>action\<in>set (map fst steps). lpp_no_action_scope_safe rest action"
   and nonempty: "steps\<noteq>[]"
   and injective: "inj r" and program: "lp_cut_source_program P"
   and separated: "r ` S \<inter> (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}"
 shows "(map (lp_cut_scope_entry r)
   (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))) @ bs,
   map (lp_cut_scope_entry r)
   (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt))) @ bs)
   \<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
 by (rule lpp_owned_delta_scope_trace[OF
   lpp_no_return_trace_owned_progress[OF checked inverse safe boundaries support scopes nonempty]
   injective program separated])

ML \<open>
val checked = [@{thm lpp_no_return_trace_owned_sound}, @{thm lpp_no_return_trace_owned_progress},
 @{thm lpp_no_return_trace_saved_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked owned return trace" else ();
\<close>
end
