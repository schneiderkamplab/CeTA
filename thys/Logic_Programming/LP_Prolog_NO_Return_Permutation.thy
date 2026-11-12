theory LP_Prolog_NO_Return_Permutation
 imports LP_Prolog_NO_Return_Ordinary LP_Cut_NO_Permutation_Rows
begin

fun lpp_no_return_permutation where
 "lpp_no_return_permutation fuel P k V images swaps
   ((LPCClause (LPCAtom a#gs) c m,payload)#saved) tt =
   (let sigma=lpc_mgu_substitution V images;
        rename=\<lambda>v. Var (lpc_no_permute swaps v);
        hs=map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. sigma (lp_prefix k v)))\<cdot>rename)) (snd (P!c)) @
           map (lp_cut_map (\<lambda>t. (t\<cdot>sigma)\<cdot>rename)) gs;
        result=map (\<lambda>t. (t\<cdot>sigma)\<cdot>rename) payload
    in lpp_no_clear P (LPCClause (LPCAtom a#gs) c m#map fst saved) \<and>
       lpc_no_return_resolve_permutation fuel P a gs c m saved payload k V images swaps hs result \<and>
       tt=(LPCGoals hs,result)#saved)"
| "lpp_no_return_permutation fuel P k V images swaps ss tt = False"

lemma lpp_no_return_permutation_sound:
 assumes checked: "lpp_no_return_permutation fuel P k V images swaps ss tt"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>lpp_builtin_source P U"
 using checked
proof (induct fuel P k V images swaps ss tt rule: lpp_no_return_permutation.induct)
 case (1 fuel P k V images swaps a gs c m payload saved tt)
 have clear: "lpp_no_clear P (map fst ((LPCClause (LPCAtom a#gs) c m,payload)#saved))" by simp
 have active: "lpc_prefix_active ((LPCClause (LPCAtom a#gs) c m,payload)#saved)" by simp
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ((LPCClause (LPCAtom a#gs) c m,payload)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>lp_cut_mgu_source P"
   using 1 lpc_no_return_resolve_permutation_attach_sound[where rest=rest, THEN lpc_answer_transition_erases]
   by (auto simp: Let_def lpc_attach_answers_erases)
 show ?case using actual lpp_no_return_clear_attach[OF active clear, of rest]
   by (simp add: lp_prolog_source_def)
qed simp_all

ML \<open>
val checked = [@{thm lpp_no_return_permutation_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted Prolog return permutation" else ();
\<close>
end
