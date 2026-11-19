theory DP_Checkpoint_Annotation
 imports DP_Checkpoint_Annotation_Syntax
begin

lemma checkpoint_pending_arguments_transport:
 assumes pending: "checkpoint_pending_arguments C N R f old s"
 and step: "(s,t)\<in>(Trs.rstep R)\<^sup>*"
 shows "checkpoint_pending_arguments C N R f old t"
proof -
 obtain children tail where shape: "old=Fun N [checkpoint_skeleton C children]#tail"
 and prefix: "(Fun f [children],s)\<in>(Trs.rstep R)\<^sup>*"
 using pending by (auto simp: checkpoint_pending_arguments_def)
 have extended: "(Fun f [children],t)\<in>(Trs.rstep R)\<^sup>*"
 by (rule rtrancl_trans[OF prefix step])
 show ?thesis unfolding checkpoint_pending_arguments_def
 by (rule exI[of _ children], rule exI[of _ tail]) (use shape extended in simp)
qed

lemma checkpoint_pending_ground_transport:
 assumes pending: "checkpoint_pending_ground C R f s p"
 and step: "(s,t)\<in>(Trs.rstep R)\<^sup>*"
 and equal: "checkpoint_skeleton C p=checkpoint_skeleton C q"
 shows "checkpoint_pending_ground C R f t q"
proof -
 obtain initial where shape: "checkpoint_skeleton C initial=checkpoint_skeleton C p"
 and prefix: "(Fun f [initial],s)\<in>(Trs.rstep R)\<^sup>*"
 using pending by (auto simp: checkpoint_pending_ground_def)
 have extended: "(Fun f [initial],t)\<in>(Trs.rstep R)\<^sup>*"
 by (rule rtrancl_trans[OF prefix step])
 show ?thesis unfolding checkpoint_pending_ground_def
 by (rule exI[of _ initial]) (use shape equal extended in simp)
qed

lemma checkpoint_pending_list_transport:
 assumes pending: "checkpoint_pending_list C L N Z S R f old s h"
 and step: "(s,t)\<in>(Trs.rstep R)\<^sup>*"
 and equal: "checkpoint_skeleton C h=checkpoint_skeleton C k"
 shows "checkpoint_pending_list C L N Z S R f old t k"
proof -
 obtain initial param where shape:
 "old=checkpoint_skeleton C h#checkpoint_forest N Z S (checkpoint_skeleton C initial)"
 and guard: "checkpoint_guard C L param"
 and prefix: "(Fun f [initial,param],s)\<in>(Trs.rstep R)\<^sup>*"
 using pending by (auto simp: checkpoint_pending_list_def)
 have extended: "(Fun f [initial,param],t)\<in>(Trs.rstep R)\<^sup>*"
 by (rule rtrancl_trans[OF prefix step])
 show ?thesis unfolding checkpoint_pending_list_def
 by (rule exI[of _ initial], rule exI[of _ param]) (use shape guard equal extended in simp)
qed

lemma checkpoint_atom_transport:
 assumes safe: "checkpoint_skeleton_safe C R"
 and steps: "list_all2 (\<lambda>s t. (s,t)\<in>(Trs.rstep R)\<^sup>*) ss ts"
 and bounded: "checkpoint_atom_bounded (length ss) atom"
 and holds: "checkpoint_atom_holds C L N Z S R old atom ss"
 shows "checkpoint_atom_holds C L N Z S R old atom ts"
proof -
 have step: "\<And>i. i<length ss \<Longrightarrow> (ss!i,ts!i)\<in>(Trs.rstep R)\<^sup>*"
 using steps by (simp add: list_all2_conv_all_nth)
 have equal: "\<And>i. i<length ss \<Longrightarrow> checkpoint_skeleton C (ss!i)=checkpoint_skeleton C (ts!i)"
 by (rule checkpoint_skeleton_rsteps[OF safe], rule step, assumption)
 show ?thesis using bounded holds
 proof (cases atom)
  case (CP_Exact i) then show ?thesis using bounded holds equal by (simp add: checkpoint_atom_bounded_def)
 next
  case (CP_Split i j) then show ?thesis using bounded holds equal by (simp add: checkpoint_atom_bounded_def)
 next
  case (CP_Prefix i) then show ?thesis using bounded holds equal by (simp add: checkpoint_atom_bounded_def)
 next
  case (CP_Strict i) then show ?thesis using bounded holds equal by (simp add: checkpoint_atom_bounded_def)
 next
  case (CP_Guard i) then show ?thesis using bounded holds equal by (simp add: checkpoint_atom_bounded_def checkpoint_guard_def)
 next
  case (CP_Arguments f i) then show ?thesis using bounded holds
   by (auto simp: checkpoint_atom_bounded_def intro: checkpoint_pending_arguments_transport step)
 next
  case (CP_Ground f i j) then show ?thesis using bounded holds
   by (auto simp: checkpoint_atom_bounded_def intro: checkpoint_pending_ground_transport step equal)
 next
  case (CP_List f i j) then show ?thesis using bounded holds
   by (auto simp: checkpoint_atom_bounded_def intro: checkpoint_pending_list_transport step equal)
 qed
qed

text \<open>All branches must be checked by a transition checker. A nonempty
inventory alone provides no evidence that a rule establishes any branch.\<close>
definition checkpoint_clause_holds where
 "checkpoint_clause_holds C L N Z S R old clause ts =
 (list_all (checkpoint_atom_bounded (length ts)) clause \<and>
 list_all (\<lambda>a. checkpoint_atom_holds C L N Z S R old a ts) clause)"

lemma checkpoint_clause_transport:
 assumes safe: "checkpoint_skeleton_safe C R"
 and steps: "list_all2 (\<lambda>s t. (s,t)\<in>(Trs.rstep R)\<^sup>*) ss ts"
 and holds: "checkpoint_clause_holds C L N Z S R old clause ss"
 shows "checkpoint_clause_holds C L N Z S R old clause ts"
 using holds steps checkpoint_atom_transport[OF safe steps]
 by (auto simp: checkpoint_clause_holds_def list_all_iff list_all2_conv_all_nth)


definition checkpoint_annotation_holds where
 "checkpoint_annotation_holds C L N Z S R table old t =
 (case t of Var x \<Rightarrow> False | Fun f ts \<Rightarrow>
  list_ex (\<lambda>(g,n,clause). f=g \<and> length ts=n \<and>
   checkpoint_clause_holds C L N Z S R old clause ts) table)"

lemma checkpoint_annotation_transport:
 assumes safe: "checkpoint_skeleton_safe C R"
 and roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root U l"
 and marked: "f\<in>U"
 and steps: "(Fun f ss,t)\<in>(Trs.rstep R)\<^sup>*"
 and holds: "checkpoint_annotation_holds C L N Z S R table old (Fun f ss)"
 shows "checkpoint_annotation_holds C L N Z S R table old t"
proof -
 obtain ts where t: "t=Fun f ts"
  using checkpoint_control_root_steps[where R=R and K=U, OF _ marked steps] roots by blast
 have arguments: "list_all2 (\<lambda>s t. (s,t)\<in>(Trs.rstep R)\<^sup>*) ss ts"
  by (rule checkpoint_control_argument_steps[OF _ marked steps[unfolded t]]) (use roots in blast)
 have len: "length ss=length ts" using arguments by (simp add: list_all2_conv_all_nth)
 obtain clause where entry: "(f,length ss,clause)\<in>set table"
 and before: "checkpoint_clause_holds C L N Z S R old clause ss"
 using holds by (auto simp: checkpoint_annotation_holds_def list_ex_iff)
 have after: "checkpoint_clause_holds C L N Z S R old clause ts"
 by (rule checkpoint_clause_transport[OF safe arguments before])
 show ?thesis unfolding checkpoint_annotation_holds_def t
 apply (simp only: term.case list_ex_iff)
 apply (rule bexI[of _ "(f,length ss,clause)"])
 using after entry len by auto
qed

ML \<open>
val thms = @{thms checkpoint_pending_arguments_transport checkpoint_pending_ground_transport checkpoint_pending_list_transport checkpoint_atom_transport checkpoint_clause_transport checkpoint_annotation_transport};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted annotation transport" else ();
\<close>
end
