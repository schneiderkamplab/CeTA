theory LP_Prolog_NO_Renamed_Permutation
 imports LP_Prolog_NO_Renamed_Ordinary LP_Prolog_NO_Return_Permutation
begin

lemma lpp_no_return_permutation_renamed_sound:
 assumes checked: "lpp_no_return_permutation fuel P k V images swaps ss tt"
   and inverse: "\<And>z. p (p z) = z"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter>
     p ` lpc_no_resolve_permutation_support P k V swaps = {}"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>lpp_builtin_source P U"
 using checked safe
proof (induct fuel P k V images swaps ss tt rule: lpp_no_return_permutation.induct)
 case (1 fuel P k V images swaps a gs c m payload saved tt)
 have clear: "lpp_no_clear P (map fst (lpc_no_rename_rows p extra
   ((LPCClause (LPCAtom a#gs) c m,payload)#saved)))"
   by (simp add: lpp_no_rename_rows_clear)
 have active: "lpc_prefix_active (lpc_no_rename_rows p extra
   ((LPCClause (LPCAtom a#gs) c m,payload)#saved))"
   by (simp add: lpc_no_rename_rows_active)
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra
     ((LPCClause (LPCAtom a#gs) c m,payload)#saved))),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))\<in>lp_cut_mgu_source P"
   using 1 lpc_no_permutation_rows_renamed[OF _ inverse, where rest=rest,
     THEN lpc_answer_transition_erases]
   by (auto simp: Let_def lpc_attach_answers_erases)
 show ?case using actual lpp_no_return_clear_attach[OF active clear, of rest]
   by (simp add: lp_prolog_source_def)
qed simp_all

ML \<open>
val checked = [@{thm lpp_no_return_permutation_renamed_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed Prolog permutation" else ();
\<close>
end
