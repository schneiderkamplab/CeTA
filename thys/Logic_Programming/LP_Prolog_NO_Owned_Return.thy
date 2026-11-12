theory LP_Prolog_NO_Owned_Return
 imports LP_Cut_NO_Attachment_Scopes
begin

lemma lpc_no_owned_term_map:
 "lpc_no_owned_suffix (map (lp_cut_entry_map f) ss) = lpc_no_owned_suffix ss"
proof -
 have barrier: "(LPCBarrier m\<in>set (map (lp_cut_entry_map f) es)) = (LPCBarrier m\<in>set es)"
   for m es
 proof (induct es)
  case Nil then show ?case by simp
 next
  case (Cons e es)
  then show ?case by (cases e) auto
 qed
 show ?thesis by (cases ss rule: lpc_no_owned_suffix.cases)
   (simp_all add: barrier del: set_map)
qed

lemma lpc_no_return_eval_active:
 "lpc_prefix_active (lpc_return_eval eta ss) = lpc_prefix_active ss"
 by (cases ss rule: lpc_prefix_active.cases) (simp_all add: lpc_return_eval_def)

lemma lpc_no_renamed_attachment_owned:
 assumes active: "lpc_prefix_active ss"
 shows "lpc_no_owned_suffix (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))) =
   lpc_no_owned_suffix (map fst ss)"
proof -
 have live: "lpc_prefix_active (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))"
   using active by (simp add: lpc_no_return_eval_active lpc_no_rename_rows_active)
 have erase: "map fst (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)) =
   map (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar))
    (map (lp_cut_entry_map (\<lambda>t. t\<cdot>(Var\<circ>p))) (map fst ss))"
   by (simp add: lpc_return_eval_def lpc_no_rename_rows_def map_map o_def case_prod_unfold)
 show ?thesis by (simp only: lpc_no_attachment_owned[OF live] erase lpc_no_owned_term_map)
qed

definition lpp_no_return_owned_boundary where
 "lpp_no_return_owned_boundary ss tt =
   (lpc_prefix_active ss \<and> lpc_no_owned_suffix (map fst ss) \<and> tt\<noteq>[] \<and>
    (lpc_no_rows_have_frame tt \<longrightarrow> lpc_no_rows_have_frame ss))"

lemma lpp_no_return_owned_step:
 assumes checked: "lpp_no_return_step fuel P reserved ss action tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_step_support P ss action = {}"
   and scopes: "lpp_no_action_scope_safe rest action"
   and boundary: "lpp_no_return_owned_boundary ss tt"
   and support: "lpc_no_rows_scopes tt \<subseteq> S"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>lpp_owned_delta_relation P
    (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)) S"
proof -
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
   by (rule lpp_no_return_step_renamed_sound[OF checked inverse safe scopes])
 have active: "lpc_prefix_active ss" and owned: "lpc_no_owned_suffix (map fst ss)"
   and nonempty: "tt\<noteq>[]"
   and frames: "lpc_no_rows_have_frame tt \<Longrightarrow> lpc_no_rows_have_frame ss"
   using boundary by (auto simp: lpp_no_return_owned_boundary_def)
 have delta: "((\<Union>e\<in>set (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt))). lp_cut_entry_scopes e) -
   (\<Union>e\<in>set (lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))). lp_cut_entry_scopes e)) \<subseteq> S"
 proof (rule subset_trans[OF lpc_no_attachment_delta_bound])
   show "lpc_no_rows_have_frame (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)) \<Longrightarrow>
     lpc_no_rows_have_frame (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss))"
     using frames by (simp only: lpc_no_rows_frames_renamed_eval)
   show "lpc_no_rows_scopes (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)) \<subseteq> S"
     using support by (simp only: lpc_no_rows_scopes_renamed_eval)
 qed
 show ?thesis using actual delta nonempty owned
   lpc_no_renamed_attachment_owned[OF active, of rest p extra]
   by (auto simp: lpp_owned_delta_relation_def lpc_return_eval_def lpc_no_rename_rows_def)
qed

ML \<open>
val checked = [@{thm lpc_no_owned_term_map}, @{thm lpc_no_return_eval_active},
 @{thm lpc_no_renamed_attachment_owned}, @{thm lpp_no_return_owned_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked owned return step" else ();
\<close>
end
