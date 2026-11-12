theory LP_Cut_NO_Ambient_Interface_Test
 imports LP_Cut_NO_Renamed_Return
begin

definition ambient_no_substitution :: "string \<Rightarrow> (string,string) term" where
 "ambient_no_substitution = lpc_mgu_substitution [''$$X''] [Fun ''a'' []]"
definition ambient_no_rename where
 "ambient_no_rename = lpc_no_swap ''$$X'' ''fresh''"

lemma ambient_no_old_private_name_is_preserved:
 "lpc_conjugate_substitution ambient_no_rename ambient_no_substitution ''$$X'' = Var ''$$X''"
 by (simp add: lpc_conjugate_substitution_def ambient_no_rename_def
   ambient_no_substitution_def lpc_no_swap_def lpc_mgu_substitution_def)

lemma ambient_no_new_private_name_is_bound:
 "lpc_conjugate_substitution ambient_no_rename ambient_no_substitution ''fresh'' = Fun ''a'' []"
 by (simp add: lpc_conjugate_substitution_def ambient_no_rename_def
   ambient_no_substitution_def lpc_no_swap_def lpc_mgu_substitution_def)

lemma ambient_no_shared_caller_term_is_preserved:
 "Fun ''pair'' [Var ''$$X'',Var ''$$X'']\<cdot>
   lpc_conjugate_substitution ambient_no_rename ambient_no_substitution =
   Fun ''pair'' [Var ''$$X'',Var ''$$X'']"
 by (simp add: ambient_no_old_private_name_is_preserved)

lemma ambient_no_unrenamed_witness_captures_caller:
 "ambient_no_substitution ''$$X'' \<noteq> Var ''$$X''"
 by (simp add: ambient_no_substitution_def lpc_mgu_substitution_def)

lemma ambient_no_noninjective_map_loses_caller:
 "lpc_conjugate_substitution (\<lambda>x::string. ''X'') Var ''Y'' \<noteq> (Var ''Y'' :: (string,string) term)"
 by (simp add: lpc_conjugate_substitution_def)

ML \<open>
val checked = [@{thm ambient_no_old_private_name_is_preserved},
 @{thm ambient_no_new_private_name_is_bound}, @{thm ambient_no_shared_caller_term_is_preserved},
 @{thm ambient_no_unrenamed_witness_captures_caller}, @{thm ambient_no_noninjective_map_loses_caller}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted caller-only variable regression" else ();
\<close>
end
