theory LP_Prolog_NO_Permutation
 imports LP_Cut_NO_Return_Permutation LP_Prolog_NO_Pumping
begin

fun lpp_no_plain_permutation where
 "lpp_no_plain_permutation fuel P k V images swaps
   (LPCClause (LPCAtom a#gs) c m#saved) tt =
   (lpp_no_clear P (LPCClause (LPCAtom a#gs) c m#saved) \<and>
    lpc_no_resolve_permutation fuel P a gs c m saved k V images swaps tt)"
| "lpp_no_plain_permutation fuel P k V images swaps ss tt = False"

lemma lpp_no_plain_permutation_sound:
 "lpp_no_plain_permutation fuel P k V images swaps ss tt \<Longrightarrow>
   (lp_cut_state_eval ss LPIVar,lp_cut_state_eval tt LPIVar)\<in>lpp_builtin_source P U"
 by (induct fuel P k V images swaps ss tt rule: lpp_no_plain_permutation.induct)
   (auto simp: lp_prolog_source_def lp_cut_state_map_def lpp_builtin_active_def lpp_undefined_def
     dest: lpc_no_resolve_permutation_sound)

ML \<open>
val checked = [@{thm lpp_no_plain_permutation_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted plain Prolog permutation" else ();
\<close>
end
