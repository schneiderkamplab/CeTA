theory LP_Prolog_NO_Probe_Check
 imports LP_Prolog_NO_Probe LP_Cut_NO_Renamed_Control
begin

lemma lpp_no_return_probe_cases:
 assumes "lpp_no_return_probe m n ss tt"
 obtains f g argv gs payload saved where
   "lpp_probe_name f"
   "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),payload)#saved"
   "lp_cut_fresh m (LPCGoals gs#map fst saved)"
   "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
   "tt=lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs payload saved"
proof -
 obtain row saved where s: "ss=row#saved"
   using assms by (cases ss) (auto simp: lpp_no_return_probe_def)
 obtain entry payload where r: "row=(entry,payload)" by (cases row) auto
 obtain goals where e: "entry=LPCGoals goals"
   using assms unfolding s r by (cases entry) (auto simp: lpp_no_return_probe_def)
 obtain goal gs where gs: "goals=goal#gs"
   using assms unfolding s r e by (cases goals) (auto simp: lpp_no_return_probe_def)
 obtain atom where atom: "goal=LPCAtom atom"
   using assms unfolding s r e gs by (cases goal) (auto simp: lpp_no_return_probe_def)
 obtain symbol args where t: "atom=Fun symbol args"
   using assms unfolding s r e gs atom by (cases atom) (auto simp: lpp_no_return_probe_def)
 obtain f where f: "symbol=LPCUser f"
   using assms unfolding s r e gs atom t by (cases symbol) (auto simp: lpp_no_return_probe_def)
 obtain arg tail where args: "args=arg#tail"
   using assms unfolding s r e gs atom t f by (cases args) (auto simp: lpp_no_return_probe_def)
 have tail: "tail=[]"
   using assms unfolding s r e gs atom t f args
   by (cases tail) (auto simp: lpp_no_return_probe_def split: Term.term.splits lp_cut_symbol.splits)
 obtain symbol2 argv where arg: "arg=Fun symbol2 argv"
   using assms unfolding s r e gs atom t f args tail
   by (cases arg) (auto simp: lpp_no_return_probe_def)
 obtain g where g: "symbol2=LPCUser g"
   using assms unfolding s r e gs atom t f args tail arg
   by (cases symbol2) (auto simp: lpp_no_return_probe_def)
 show thesis
   using assms that[of f g argv gs payload saved]
   by (simp add: s r e gs atom t f args tail arg g lpp_no_return_probe_def)
qed

ML \<open>writeln "PROBE_CASES_CHECKED"\<close>

lemma lpp_no_return_probe_sound:
 assumes checked: "lpp_no_return_probe m n ss tt"
   and sm: "m\<notin>lpc_rest_scopes rest"
   and sn: "n\<notin>lpc_rest_scopes rest"
 shows "(lpc_attach rest (lpc_return_eval eta ss),
   lpc_attach rest (lpc_return_eval eta tt))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
 using checked
 by (cases rule: lpp_no_return_probe_cases)
   (auto intro: lpp_no_probe_return_attach[OF _ _ _ sm sn])

lemma lpp_no_probe_stack_rename:
 "lpc_no_rename_rows p extra (lpp_probe_stack a keep m n gs payload saved) =
  lpp_probe_stack (a\<cdot>(Var\<circ>p)) keep m n
   (map (lp_cut_map (\<lambda>t. t\<cdot>(Var\<circ>p))) gs)
   (map (\<lambda>t. t\<cdot>(Var\<circ>p)) payload @ extra)
   (lpc_no_rename_rows p extra saved)"
 by (cases keep)
   (simp_all add: lpc_no_rename_rows_def lpp_probe_stack_def lpp_probe_goals_def lpp_probe_else_def)

lemma lpp_no_return_probe_renamed:
 assumes checked: "lpp_no_return_probe m n ss tt"
 shows "lpp_no_return_probe m n
   (lpc_no_rename_rows p extra ss) (lpc_no_rename_rows p extra tt)"
proof -
 obtain f g argv gs payload saved where that:
   "lpp_probe_name f"
   "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),payload)#saved"
   "lp_cut_fresh m (LPCGoals gs#map fst saved)"
   "lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved)"
   "tt=lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs payload saved"
   by (rule lpp_no_return_probe_cases[OF checked]) blast
 have fm: "lp_cut_fresh m
   (LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>(Var\<circ>p))) gs)#
      map fst (lpc_no_rename_rows p extra saved))"
   using lp_cut_fresh_state_map[of m "\<lambda>t. t\<cdot>(Var\<circ>p)" "LPCGoals gs#map fst saved"] that(3)
   by (simp add: lpc_no_rename_rows_erases lp_cut_state_map_def)
 have fn: "lp_cut_fresh n
   (LPCBarrier m#LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>(Var\<circ>p))) gs)#
      map fst (lpc_no_rename_rows p extra saved))"
   using lp_cut_fresh_state_map[of n "\<lambda>t. t\<cdot>(Var\<circ>p)" "LPCBarrier m#LPCGoals gs#map fst saved"] that(4)
   by (simp add: lpc_no_rename_rows_erases lp_cut_state_map_def)
 show ?thesis
   unfolding that(2,5)
   apply (simp only: lpp_no_probe_stack_rename)
   using that(1) fm fn
   by (simp add: lpp_no_return_probe_def lpc_no_rename_rows_def)
qed

lemma lpp_no_return_probe_renamed_sound:
 assumes checked: "lpp_no_return_probe m n ss tt"
   and sm: "m\<notin>lpc_rest_scopes rest"
   and sn: "n\<notin>lpc_rest_scopes rest"
 shows "(lpc_attach rest (lpc_return_eval eta (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval eta (lpc_no_rename_rows p extra tt)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
 by (rule lpp_no_return_probe_sound[OF lpp_no_return_probe_renamed[OF checked] sm sn])

lemma lpp_no_plain_probe_attachment:
 "lpc_attach [] (lpc_return_eval eta (map (\<lambda>e. (e,[])) ss)) = lp_cut_state_eval ss eta"
proof (induct ss)
 case Nil then show ?case by (simp add: lpc_return_eval_def lp_cut_state_map_def)
next
 case (Cons a ss) then show ?case
   by (cases a) (simp_all add: lpc_return_eval_def lp_cut_state_map_def)
qed

lemma lpp_no_plain_probe_sound:
 assumes "lpp_no_plain_probe m n ss tt"
 shows "(lp_cut_state_eval ss eta,lp_cut_state_eval tt eta)
   \<in>lpp_builtin_source P (lpp_stable_source_builtin operation)"
 using lpp_no_return_probe_sound[of m n "map (\<lambda>e. (e,[])) ss"
   "map (\<lambda>e. (e,[])) tt" "[]" eta P operation] assms
 by (auto simp: lpp_no_plain_probe_def lpp_no_plain_probe_attachment)

ML \<open>
val checked = [@{thm lpp_no_return_probe_sound}, @{thm lpp_no_return_probe_renamed},
 @{thm lpp_no_return_probe_renamed_sound}, @{thm lpp_no_plain_probe_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked probe renaming" else ();
\<close>
end
