theory LP_Cut_NO_Attachment_Scopes
 imports LP_Source_Owned_Delta
begin

fun lpc_no_return_frame where
 "lpc_no_return_frame (LPCBarrier m) = False"
| "lpc_no_return_frame e = True"

lemma lpc_no_return_frame_map[simp]:
 "lpc_no_return_frame (lp_cut_entry_map f e) = lpc_no_return_frame e"
 by (cases e) simp_all

definition lpc_no_rows_scopes where
 "lpc_no_rows_scopes ss = (\<Union>e\<in>set (map fst ss). lp_cut_entry_scopes e)"

definition lpc_no_rows_have_frame where
 "lpc_no_rows_have_frame ss = (\<exists>e\<in>set (map fst ss). lpc_no_return_frame e)"

lemma lpc_no_attachment_frame_scopes_exact:
 "lp_cut_entry_scopes (lpc_attach_frame rest (e,eta)) = lp_cut_entry_scopes e \<union>
  (if lpc_no_return_frame e then lpc_rest_scopes rest else {})"
 by (cases e) auto

lemma lpc_no_attachment_scopes_exact:
 "(\<Union>e\<in>set (lpc_attach rest ss). lp_cut_entry_scopes e) =
  lpc_no_rows_scopes ss \<union>
  (if lpc_no_rows_have_frame ss then lpc_rest_scopes rest else {})"
 by (induct ss) (auto simp: lpc_no_rows_scopes_def lpc_no_rows_have_frame_def
   lpc_no_attachment_frame_scopes_exact split: prod.splits if_splits)

lemma lpc_no_attachment_delta_bound:
 assumes frames: "lpc_no_rows_have_frame tt \<Longrightarrow> lpc_no_rows_have_frame ss"
 shows "((\<Union>e\<in>set (lpc_attach rest tt). lp_cut_entry_scopes e) -
  (\<Union>e\<in>set (lpc_attach rest ss). lp_cut_entry_scopes e)) \<subseteq> lpc_no_rows_scopes tt"
 using frames by (simp only: lpc_no_attachment_scopes_exact) auto

lemma lpc_no_rows_scopes_renamed_eval:
 "lpc_no_rows_scopes (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)) = lpc_no_rows_scopes ss"
 by (auto simp: lpc_no_rows_scopes_def lpc_return_eval_def lpc_no_rename_rows_def)

lemma lpc_no_rows_frames_renamed_eval:
 "lpc_no_rows_have_frame (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)) = lpc_no_rows_have_frame ss"
 by (auto simp: lpc_no_rows_have_frame_def lpc_return_eval_def lpc_no_rename_rows_def case_prod_unfold)

lemma lpc_no_attach_barrier_iff[simp]:
 "(LPCBarrier m = lpc_attach_frame rest (e,eta)) = (LPCBarrier m = e)"
 by (cases e) simp_all

lemma lpc_no_attachment_owned:
 assumes active: "lpc_prefix_active ss"
 shows "lpc_no_owned_suffix (lpc_attach rest ss) = lpc_no_owned_suffix (map fst ss)"
proof -
 have barrier: "(LPCBarrier m\<in>set (lpc_attach rest saved)) = (LPCBarrier m\<in>set (map fst saved))"
   for m saved
   by (auto simp: image_iff case_prod_unfold; force)
 obtain e eta saved where shape: "ss=(e,eta)#saved"
   using active by (cases ss) auto
 show ?thesis
 proof (cases e)
  case (LPCGoals gs)
  obtain g tail where goals: "gs=g#tail"
    using active shape LPCGoals by (cases gs) auto
  show ?thesis by (cases g) (simp_all add: shape LPCGoals goals barrier del: set_map)
 next
  case (LPCClause gs c m)
  show ?thesis by (simp add: shape LPCClause)
 next
  case (LPCBarrier m)
  show ?thesis by (simp add: shape LPCBarrier)
 qed
qed

ML \<open>
val checked = [@{thm lpc_no_attachment_scopes_exact}, @{thm lpc_no_attachment_delta_bound},
 @{thm lpc_no_rows_scopes_renamed_eval}, @{thm lpc_no_rows_frames_renamed_eval},
 @{thm lpc_no_attachment_owned}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return attachment scope transport" else ();
\<close>
end
