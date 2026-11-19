theory LP_Prolog_Attached_Univ_Actual_Path
 imports LP_Prolog_Acquired_Univ_Product
begin

lemma lpp_attached_univ_actual_path:
 fixes env :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [LPIFun f ts,requested])#pending),env)#saved)) event result"
 shows "event=None \<and> (result=[] \<or> (\<exists>middle.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_attach_answers rest ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
      LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved)) None middle \<and>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain middle None result))"
proof -
 have domain: "lpp_univ_view_domain (LPIFun f ts) requested" by simp
 have path: "event=None \<and> (result=[] \<or>
   (lpc_answer_transition P
    ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
      LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)),env)#lpc_attach_answers rest saved) None
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)),env)#lpc_attach_answers rest saved) \<and>
    lpc_answer_transition P
    ((LPCGoals (LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#
      (pending @ map (lp_cut_map (\<lambda>t. lp_ieval t env)) rest)),env)#lpc_attach_answers rest saved) None result))"
  using lpp_observer_univ_actual_normalized_path[OF domain step[unfolded lpc_attach_answers_def, simplified]] by (simp add: lpc_attach_answers_def)
 have lift: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   ((LPCGoals (LPCUnify a b#gs),eta)#es) ev ys"
  if "lpc_answer_transition P ((LPCGoals (LPCUnify a b#gs),eta)#es) ev ys" for a b gs eta es ev ys
  using that by (auto simp: lpp_domain_answers_def intro!: lpp_answer_transition.base simp: lpp_builtin_active_def)
 show ?thesis using path lift
  by (auto simp: lpc_attach_answers_def dest: lift)
qed

ML \<open>
val checked = @{thms lpp_attached_univ_actual_path};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached actual normalization" else ();
val _ = writeln "ATTACHED_ACTUAL_NORMALIZATION_CHECKED";
\<close>
end
