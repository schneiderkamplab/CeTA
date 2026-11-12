theory LP_Cut_NO_Permutation_Rows
 imports LP_Cut_NO_Renamed_Permutation LP_Cut_NO_Action_Support
begin

definition lpc_no_resolve_permutation_support where
 "lpc_no_resolve_permutation_support P k V swaps =
   (set V \<union> lpc_no_permutation_support swaps) \<union> lp_prefix k ` lpc_no_program_vars P"

lemma lpc_no_resolve_permutation_support_finite[simp]:
 "finite (lpc_no_resolve_permutation_support P k V swaps)"
 by (simp add: lpc_no_resolve_permutation_support_def)

lemma lpc_no_permutation_rows_renamed:
 assumes checked: "lpc_no_return_resolve_permutation fuel P a gs c m saved payload k V images swaps hs result"
   and inverse: "\<And>z. p (p z) = z"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpc_no_resolve_permutation_support P k V swaps = {}"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCClause (LPCAtom a#gs) c m,payload)#saved)))) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows p extra ((LPCGoals hs,result)#saved))))"
proof -
 have index: "c<length P" and lengths: "length V=length images" using checked
   by (auto simp: lpc_no_return_resolve_permutation_def lpc_no_resolve_permutation_def lpc_check_mgu_def)
 have fresh: "vars_term t \<inter> (p \<circ> lp_prefix k) ` lpc_no_program_vars P = {}"
   if "t\<in>set extra" for t
   using safe that by (auto simp: lpc_no_resolve_permutation_support_def)
 have outside: "z\<notin>p ` (set V \<union> lpc_no_permutation_support swaps)"
   if "z\<in>\<Union>(vars_term ` set extra)" for z
   using safe that by (auto simp: lpc_no_resolve_permutation_support_def)
 have fixed: "map (\<lambda>t. (t\<cdot>lpc_conjugate_substitution p (lpc_mgu_substitution V images))\<cdot>
     (\<lambda>v. Var (lpc_no_permute (map (\<lambda>(x,y). (p x,p y)) swaps) v))) extra = extra"
   by (rule lpc_renamed_permutation_fixes_ambient[OF inverse lengths outside])
 note step = lpc_no_return_permutation_renamed_ambient[where rest=rest and extra=extra and saved="lpc_no_rename_rows p extra saved",
   OF checked inverse
   lpc_no_program_head_vars[OF index] lpc_no_program_body_vars[OF index] fresh fixed]
 show ?thesis using step by (simp add: lpc_no_rename_rows_def)
qed

ML \<open>
val checked = [@{thm lpc_no_permutation_rows_renamed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted permutation rows" else ();
\<close>
end
