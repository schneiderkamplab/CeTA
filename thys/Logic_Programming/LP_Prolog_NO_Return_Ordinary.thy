theory LP_Prolog_NO_Return_Ordinary
 imports LP_Cut_NO_Return_Trace LP_Prolog_NO_Return_Builtin
begin

text \<open>The ordinary LP trace bridge must not execute Prolog builtins or
undefined calls. A nonempty active prefix prevents attachment from exposing a
caller goal before the checked prefix has made its step.\<close>

lemma lpp_no_return_clear_attach:
 assumes active: "lpc_prefix_active ss"
   and clear: "lpp_no_clear P (map fst ss)"
 shows "\<not>lpp_builtin_active lpp_builtin_signature (lpc_attach rest (lpc_return_eval LPIVar ss)) \<and>
   \<not>lpp_undefined P (lpc_attach rest (lpc_return_eval LPIVar ss))"
proof -
 obtain e payload saved where shape: "ss=(e,payload)#saved"
   using active by (cases ss) auto
 show ?thesis
 proof (cases e)
   case (LPCGoals gs)
   obtain g tail where goals: "gs=g#tail"
     using active shape LPCGoals by (cases gs) auto
   show ?thesis
   proof (cases g)
     case (LPCAtom a)
     show ?thesis using clear
       by (cases a; auto simp: shape LPCGoals goals LPCAtom lpc_return_eval_def
         lpp_builtin_active_def lpp_undefined_def split: lp_cut_symbol.splits)
   qed (simp_all add: shape LPCGoals goals lpc_return_eval_def lpp_builtin_active_def lpp_undefined_def)
 qed (simp_all add: shape lpc_return_eval_def lpp_builtin_active_def lpp_undefined_def)
qed

definition lpp_no_return_ordinary_step where
 "lpp_no_return_ordinary_step fuel P reserved ss action tt =
   (lpc_prefix_active ss \<and> lpp_no_clear P (map fst ss) \<and>
    lpc_no_return_step fuel P reserved ss action tt)"

lemma lpp_no_return_ordinary_step_sound:
 assumes checked: "lpp_no_return_ordinary_step fuel P reserved ss action tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>lpp_builtin_source P U"
proof -
 have active: "lpc_prefix_active ss" and clear: "lpp_no_clear P (map fst ss)"
   and step: "lpc_no_return_step fuel P reserved ss action tt"
   using checked by (auto simp: lpp_no_return_ordinary_step_def)
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_attach_sound[OF step scopes]]
   by (simp add: lpc_attach_answers_erases)
 show ?thesis using actual lpp_no_return_clear_attach[OF active clear, of rest]
   by (simp add: lp_prolog_source_def)
qed

ML \<open>
val checked = [@{thm lpp_no_return_clear_attach}, @{thm lpp_no_return_ordinary_step_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted Prolog ordinary return trace bridge" else ();
\<close>
end
