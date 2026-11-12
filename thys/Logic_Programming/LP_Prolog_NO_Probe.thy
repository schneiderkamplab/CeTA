theory LP_Prolog_NO_Probe
 imports LP_Prolog_NO_Return_Trace LP_Prolog_Evaluation_Probe
begin

text \<open>Entering an opaque probe is an operational step, not a successful
helper contract. Both alternatives and their environments remain in the trace.\<close>

lemma lpp_no_stable_probe_outcome:
 assumes name: "lpp_probe_name f"
 shows "lpp_stable_source_builtin operation f [LPIFun (LPCUser g) argv]
   (LPPBuiltinProbe (LPIFun (LPCUser g) argv) (f=''1:once''))"
proof -
 have domain: "lpp_probe_domain f [LPIFun (LPCUser g) argv]"
   using name by (auto simp only: lpp_probe_domain_def)
 have finite: "lpp_finite_source_builtin f [LPIFun (LPCUser g) argv]
   (LPPBuiltinProbe (LPIFun (LPCUser g) argv) (f=''1:once''))"
   by (simp only: lpp_finite_source_builtin_def name if_True lpp_probe_outcome_def domain list.sel; simp)
 have no_is: "f\<noteq>''2:is''"
   using name lpp_probe_legacy_flags(5,10,15) unfolding lpp_probe_name_def by metis
 have no_compare: "lpp_source_comparison f=None"
   using name lpp_probe_legacy_flags(3,8,13) unfolding lpp_probe_name_def by metis
 show ?thesis by (simp only: lpp_stable_source_builtin_def finite no_is if_False no_compare option.case; simp)
qed

lemma lpp_no_probe_source:
 assumes name: "lpp_probe_name f"
   and fm: "lp_cut_fresh m (LPCGoals gs#es)"
   and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#es)"
 shows "(LPCGoals (LPCAtom (LPIFun (LPCUser f) [LPIFun (LPCUser g) argv])#gs)#es,
   LPCGoals (lpp_probe_goals (LPIFun (LPCUser g) argv) (f=''1:once'') m gs)#LPCBarrier n#
   LPCGoals (lpp_probe_else (f=''1:once'') gs)#LPCBarrier m#es)
   \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
proof -
 have selected: "(f,1)\<in>lpp_builtin_signature"
   using lpp_probe_selected[of f "[LPIFun (LPCUser g) argv]"] name
   by (auto simp: lpp_probe_domain_def)
 have actual: "(LPCGoals (LPCAtom (LPIFun (LPCUser f) [LPIFun (LPCUser g) argv])#gs)#es,
   LPCGoals (lpp_probe_goals (LPIFun (LPCUser g) argv) (f=''1:once'') m gs)#LPCBarrier n#
   LPCGoals (lpp_probe_else (f=''1:once'') gs)#LPCBarrier m#es)
   \<in>lpp_atomic_source P lpp_builtin_signature (lpp_stable_source_builtin operation)"
   apply (rule lpp_atomic_source.probe)
   apply (rule lpp_no_stable_probe_outcome[OF name])
   using fm fn by (simp_all add: lp_cut_fresh_def)
 show ?thesis using actual selected
   by (auto simp: lp_prolog_source_def lpp_builtin_active_def)
qed

definition lpp_no_return_probe where
 "lpp_no_return_probe m n ss tt = (case ss of
   (LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),payload)#saved \<Rightarrow>
   (lpp_probe_name f \<and> lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
    lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
    tt=lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs payload saved)
 | _ \<Rightarrow> False)"

lemma lpp_no_probe_attachment:
 "lpc_attach rest (lpc_return_eval eta (lpp_probe_stack a keep m n gs payload saved)) =
   LPCGoals (lpp_probe_goals (lp_ieval a eta) keep m
     (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
       map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest))#LPCBarrier n#
   LPCGoals (lpp_probe_else keep
     (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
       map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest))#LPCBarrier m#
   lpc_attach rest (lpc_return_eval eta saved)"
 by (cases keep)
   (simp_all add: lpc_return_eval_def lpp_probe_stack_def lpp_probe_goals_def lpp_probe_else_def)

lemma lpp_no_probe_return_attach:
 assumes name: "lpp_probe_name f"
   and fm: "lp_cut_fresh m (LPCGoals gs#map fst saved)"
   and fn: "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
   and sm: "m\<notin>lpc_rest_scopes rest"
   and sn: "n\<notin>lpc_rest_scopes rest"
 shows "(lpc_attach rest (lpc_return_eval eta
     ((LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval eta
     (lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs payload saved)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
proof -
 let ?rows = "(LPCGoals gs,payload)#saved"
 let ?barrier = "(LPCBarrier m,payload)#?rows"
 have em: "lp_cut_fresh m (map fst (lpc_return_eval eta ?rows))"
   using fm lp_cut_fresh_state_map[of m "\<lambda>t. lp_ieval t eta" "LPCGoals gs#map fst saved"]
   by (simp add: lpc_return_eval_erases lp_cut_state_map_def)
 have en: "lp_cut_fresh n (map fst (lpc_return_eval eta ?barrier))"
   using fn lp_cut_fresh_state_map[of n "\<lambda>t. lp_ieval t eta" "LPCBarrier m#LPCGoals gs#map fst saved"]
   by (simp add: lpc_return_eval_erases lp_cut_state_map_def)
 have am: "lp_cut_fresh m (lpc_attach rest (lpc_return_eval eta ?rows))"
   by (rule lpc_attach_fresh_extension[OF em sm])
 have an: "lp_cut_fresh n (lpc_attach rest (lpc_return_eval eta ?barrier))"
   by (rule lpc_attach_fresh_extension[OF en sn])
 have am': "lp_cut_fresh m (LPCGoals
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
      map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)#
       lpc_attach rest (lpc_return_eval eta saved))"
   using am by (simp add: lpc_return_eval_def)
 have an': "lp_cut_fresh n (LPCBarrier m#LPCGoals
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
      map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env payload eta))) rest)#
       lpc_attach rest (lpc_return_eval eta saved))"
   using an by (simp add: lpc_return_eval_def)
 note step = lpp_no_probe_source[OF name am' an', where P=P and operation=operation
   and g=g and argv="map (\<lambda>t. lp_ieval t eta) argv"]
 show ?thesis using step
   by (simp only: lpp_no_probe_attachment; simp add: lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_no_stable_probe_outcome}, @{thm lpp_no_probe_source},
 @{thm lpp_no_probe_attachment}, @{thm lpp_no_probe_return_attach}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted probe source attachment" else ();
\<close>

end
