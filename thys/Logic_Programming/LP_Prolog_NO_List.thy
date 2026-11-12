theory LP_Prolog_NO_List
 imports LP_Prolog_NO_Probe_Check LP_Prolog_NO_List_Definition LP_Cut_NO_Return_Attachment
begin

lemma lpp_no_list_outcome:
 assumes "lpp_check_list_observation fuel t=Some held"
 shows "lpp_stable_source_builtin operation ''1:is_list'' [lp_ieval t eta]
   (if held then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 using lpp_list_observation_outcome[OF lpp_check_list_observation_sound[OF assms], of eta]
 by (simp add: lpp_stable_source_builtin_def lpp_finite_source_builtin_def
   lpp_disequality_predicate_def)

lemma lpp_no_list_attach:
 assumes checked: "lpp_check_list_observation fuel t=Some held"
 shows "(lpc_attach rest (lpc_return_eval eta
    ((LPCGoals (LPCAtom (Fun (LPCUser ''1:is_list'') [t])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval eta
    (if held then (LPCGoals gs,payload)#saved else saved)))
  \<in> lpp_builtin_source P (lpp_stable_source_builtin operation)"
proof -
 have selected: "(''1:is_list'',1)\<in>lpp_builtin_signature"
   by (simp add: lpp_builtin_signature_def)
 note outcome = lpp_no_list_outcome[OF checked, of operation eta]
 show ?thesis
 proof (cases held)
  case True
  have out: "lpp_stable_source_builtin operation ''1:is_list'' [lp_ieval t eta]
     (LPPBuiltinSuccess LPIVar)" using outcome True by simp
  note step = lpp_atomic_source.success[where U="lpp_stable_source_builtin operation"
    and f="''1:is_list''" and ts="[lp_ieval t eta]" and sigma=LPIVar
    and P=P and B=lpp_builtin_signature, OF out]
  show ?thesis using step selected True
    by (auto simp: lpc_return_eval_def lp_prolog_source_def lpp_builtin_active_def)
 next
  case False
  have out: "lpp_stable_source_builtin operation ''1:is_list'' [lp_ieval t eta]
     LPPBuiltinFailure" using outcome False by simp
  note step = lpp_atomic_source.failure[where U="lpp_stable_source_builtin operation"
    and f="''1:is_list''" and ts="[lp_ieval t eta]" and P=P and B=lpp_builtin_signature, OF out]
  show ?thesis using step selected False
    by (auto simp: lpc_return_eval_def lp_prolog_source_def lpp_builtin_active_def)
 qed
qed

lemma lpp_no_return_list_sound:
 "lpp_no_return_list fuel held ss tt \<Longrightarrow>
 (lpc_attach rest (lpc_return_eval eta ss),lpc_attach rest (lpc_return_eval eta tt))
 \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
proof (induction fuel held ss tt rule: lpp_no_return_list.induct)
 case (1 fuel held f a gs payload saved tt)
 then have name: "f=''1:is_list''" and checked: "lpp_check_list_observation fuel a=Some held"
   and target: "tt=(if held then (LPCGoals gs,payload)#saved else saved)" by auto
 show ?case unfolding name target by (rule lpp_no_list_attach[OF checked])
qed simp_all

lemma lpp_no_plain_list_sound:
 "lpp_no_plain_list fuel held ss tt \<Longrightarrow>
 (lp_cut_state_eval ss eta,lp_cut_state_eval tt eta)
 \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
 using lpp_no_return_list_sound[of fuel held "map (\<lambda>e. (e,[])) ss"
   "map (\<lambda>e. (e,[])) tt" "[]" eta P operation]
 by (simp add: lpp_no_plain_list_def lpp_no_plain_probe_attachment)

lemma lpp_check_list_observation_rename:
 "lpp_check_list_observation fuel (t\<cdot>(Var\<circ>p)) = lpp_check_list_observation fuel t"
proof (induction fuel arbitrary: t)
 case 0 then show ?case by simp
next
 case (Suc fuel)
 then show ?case by (cases t) auto
qed

lemma lpp_no_return_list_renamed:
 "lpp_no_return_list fuel held ss tt \<Longrightarrow>
 lpp_no_return_list fuel held (lpc_no_rename_rows p extra ss) (lpc_no_rename_rows p extra tt)"
 by (induction fuel held ss tt rule: lpp_no_return_list.induct)
   (auto simp: lpc_no_rename_rows_def lpp_check_list_observation_rename)

ML \<open>
val checked = [@{thm lpp_no_list_attach}, @{thm lpp_no_return_list_sound},
 @{thm lpp_no_plain_list_sound}, @{thm lpp_no_return_list_renamed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted list observation dependency" else ();
\<close>
end
