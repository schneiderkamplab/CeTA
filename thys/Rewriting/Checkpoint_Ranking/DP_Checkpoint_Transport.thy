theory DP_Checkpoint_Transport
 imports DP_Checkpoint_Path
begin

lemma checkpoint_control_nonroot_step:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and step: "(Fun f ss,t)\<in>rstep R"
 shows "(Fun f ss,t)\<in>nrrstep R"
proof -
 obtain l r D sigma where rule: "(l,r)\<in>R"
 and source: "Fun f ss=D\<langle>l\<cdot>sigma\<rangle>"
 and target: "t=D\<langle>r\<cdot>sigma\<rangle>" using step by auto
 have opaque: "checkpoint_opaque_root K l" by (rule rules[OF rule])
 have nonroot: "D\<noteq>Hole" using source opaque marked
  by (auto simp: checkpoint_opaque_root_def)
 show ?thesis by (rule nrrstepI[OF rule source target nonroot])
qed

lemma checkpoint_control_nonroot_steps:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and steps: "(Fun f ss,t)\<in>(rstep R)\<^sup>*"
 shows "(Fun f ss,t)\<in>(nrrstep R)\<^sup>*"
 using steps
proof (induct rule: rtrancl_induct)
 case base show ?case by simp
next
 case (step y z)
 have root: "\<exists>ts. y=Fun f ts"
  by (rule checkpoint_control_root_steps[where R=R and K=K, OF _ marked step.hyps(1)]) (use rules in blast)
 obtain ts where y: "y=Fun f ts" using root by blast
 have edge: "(y,z)\<in>nrrstep R"
  unfolding y by (rule checkpoint_control_nonroot_step[OF rules marked step.hyps(2)[unfolded y]])
 show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) edge])
qed

lemma checkpoint_control_argument_steps:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and steps: "(Fun f ss,Fun f ts)\<in>(rstep R)\<^sup>*"
 shows "list_all2 (\<lambda>s t. (s,t)\<in>(rstep R)\<^sup>*) ss ts"
proof -
 have nonroot: "(Fun f ss,Fun f ts)\<in>(nrrstep R)\<^sup>*"
  by (rule checkpoint_control_nonroot_steps[OF rules marked steps])
 show ?thesis using nrrsteps_equiv_num_args[OF nonroot] nrrsteps_imp_arg_rsteps[OF nonroot]
  by (simp add: list_all2_conv_all_nth)
qed

lemma checkpoint_control_saved_skeletons:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and safe: "checkpoint_skeleton_safe C R"
 and steps: "(Fun f ss,Fun f ts)\<in>(rstep R)\<^sup>*"
 shows "map (checkpoint_skeleton C) ss = map (checkpoint_skeleton C) ts"
 using checkpoint_control_argument_steps[OF rules marked steps]
 by (induct rule: list_all2_induct) (auto intro: checkpoint_skeleton_rsteps[OF safe])

lemma checkpoint_control_pending_call:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and steps: "(Fun f ss,Fun f ts)\<in>(rstep R)\<^sup>*"
 and coordinate: "i<length ss"
 and prefix: "(call,ss!i)\<in>(rstep R)\<^sup>*"
 shows "(call,ts!i)\<in>(rstep R)\<^sup>*"
proof -
 have argument: "(ss!i,ts!i)\<in>(rstep R)\<^sup>*"
  using checkpoint_control_argument_steps[OF rules marked steps] coordinate
  by (simp add: list_all2_conv_all_nth)
 show ?thesis by (rule rtrancl_trans[OF prefix argument])
qed

lemma checkpoint_argument_projection:
 assumes related: "list_all2 rel ss ts"
 and bounds: "\<And>i. i\<in>set coordinates \<Longrightarrow> i<length ss"
 shows "list_all2 rel (map ((!) ss) coordinates) (map ((!) ts) coordinates)"
 using related bounds
 by (auto simp: list_all2_conv_all_nth)

lemma checkpoint_control_projection:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and steps: "(Fun f ss,Fun f ts)\<in>(rstep R)\<^sup>*"
 and bounds: "\<And>i. i\<in>set coordinates \<Longrightarrow> i<length ss"
 shows "list_all2 (\<lambda>s t. (s,t)\<in>(rstep R)\<^sup>*)
 (map ((!) ss) coordinates) (map ((!) ts) coordinates)"
 by (rule checkpoint_argument_projection[OF checkpoint_control_argument_steps[OF rules marked steps] bounds])

lemma checked_checkpoint_argument_transport:
 assumes checked: "check_checkpoint_control U K h pairs support"
 and marked: "f\<in>U"
 and steps: "(Fun f ss,Fun f ts)\<in>(rstep (set support))\<^sup>*"
 shows "list_all2 (\<lambda>s t. (s,t)\<in>(rstep (set support))\<^sup>*) ss ts"
proof (rule checkpoint_control_argument_steps[OF _ marked steps])
 fix l r assume member: "(l,r)\<in>set support"
 show "checkpoint_opaque_root U l"
  using checked member by (auto simp: check_checkpoint_control_def list_all_iff checkpoint_support_control_correct)
qed

ML \<open>
val thms = @{thms checkpoint_control_nonroot_step checkpoint_control_nonroot_steps checkpoint_control_argument_steps checkpoint_control_saved_skeletons checkpoint_control_pending_call checkpoint_argument_projection checkpoint_control_projection checked_checkpoint_argument_transport};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted coordinate transport" else ();
\<close>
end
