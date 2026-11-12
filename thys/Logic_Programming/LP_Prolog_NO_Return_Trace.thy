theory LP_Prolog_NO_Return_Trace
 imports LP_Prolog_NO_Return_Compare LP_Prolog_NO_Return_Permutation
begin

text \<open>Reuse the existing machine NO action language. Ordinary steps retain
Prolog source dispatch, and machine actions update the active return interface.
Older integer-only receipts and unsupported actions remain explicit rejections
in this new route; existing certificate endpoints are unchanged.\<close>

fun lpp_no_return_step where
 "lpp_no_return_step fuel P reserved ss
   (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary action)))) tt =
    lpp_no_return_ordinary_step fuel P reserved ss action tt"
| "lpp_no_return_step fuel P reserved ss (LPPMIs e) tt = lpp_no_return_is e ss tt"
| "lpp_no_return_step fuel P reserved ss (LPPMCompare left right held) tt =
    lpp_no_return_compare left right held ss tt"
| "lpp_no_return_step fuel P reserved ss (LPPMInteger v) tt = lpp_no_return_integer v ss tt"
| "lpp_no_return_step fuel P reserved ss (LPPMProbe m n) tt =
    (m\<notin>set reserved \<and> n\<notin>set reserved \<and> lpp_no_return_probe m n ss tt)"
| "lpp_no_return_step fuel P reserved ss (LPPMList held) tt = lpp_no_return_list fuel held ss tt"
| "lpp_no_return_step fuel P reserved ss (LPPMResolvePermute k V images swaps) tt =
    lpp_no_return_permutation fuel P k V images swaps ss tt"
| "lpp_no_return_step fuel P reserved ss action tt = False"

lemma lpp_no_return_step_sound:
 assumes checked: "lpp_no_return_step fuel P reserved ss action tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),lpc_attach rest (lpc_return_eval LPIVar tt))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 using checked scopes
 by (induct fuel P reserved ss action tt rule: lpp_no_return_step.induct)
   (auto intro: lpp_no_return_ordinary_step_sound lpp_no_return_is_sound
     lpp_no_return_compare_sound lpp_no_return_integer_sound lpp_no_return_probe_sound lpp_no_return_list_sound lpp_no_return_permutation_sound)

fun lpp_no_return_trace where
 "lpp_no_return_trace fuel P reserved ss [] tt = (ss=tt)"
| "lpp_no_return_trace fuel P reserved ss ((action,uu)#steps) tt =
   (lpp_no_return_step fuel P reserved ss action uu \<and>
    lpp_no_return_trace fuel P reserved uu steps tt)"

lemma lpp_no_return_trace_attach_sound:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>*"
 using checked
proof (induct steps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons entry steps)
 obtain action uu where entry: "entry=(action,uu)" by (cases entry) auto
 have local_step: "lpp_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpp_no_return_trace fuel P reserved uu steps tt"
   using Cons.prems entry by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ss),
     lpc_attach rest (lpc_return_eval LPIVar uu))\<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_no_return_step_sound[OF local_step scopes])
 show ?case using actual Cons.hyps[OF local_tail] by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpp_no_return_trace_attach_progress:
 assumes checked: "lpp_no_return_trace fuel P reserved ss steps tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
   and nonempty: "steps\<noteq>[]"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>(lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain action uu tail where shape: "steps=(action,uu)#tail"
   using nonempty by (cases steps) auto
 have local_step: "lpp_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpp_no_return_trace fuel P reserved uu tail tt"
   using checked shape by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ss),
     lpc_attach rest (lpc_return_eval LPIVar uu))\<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_no_return_step_sound[OF local_step scopes])
 show ?thesis using actual lpp_no_return_trace_attach_sound[OF local_tail scopes]
   by (rule rtrancl_into_trancl2)
qed

ML \<open>
val checked = [@{thm lpp_no_return_step_sound}, @{thm lpp_no_return_trace_attach_sound},
 @{thm lpp_no_return_trace_attach_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted Prolog return-aware trace dependency" else ();
\<close>
end
