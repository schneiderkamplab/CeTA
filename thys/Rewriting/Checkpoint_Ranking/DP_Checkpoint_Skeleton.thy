theory DP_Checkpoint_Skeleton
  imports "First_Order_Rewriting.Trs"
begin

text \<open>Constructor observations of arbitrary residual terms. Every maximal
nonconstructor-rooted subterm, including a variable, is opaque. No restriction
on substitutions, normal forms, or minimal dependency chains is used.\<close>

fun checkpoint_skeleton :: "'f set \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,unit) term" where
 "checkpoint_skeleton C (Var x) = Var ()"
| "checkpoint_skeleton C (Fun f ts) =
    (if f\<in>C then Fun f (map (checkpoint_skeleton C) ts) else Var ())"

definition checkpoint_opaque_root :: "'f set \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
 "checkpoint_opaque_root C t = (\<exists>f ts. t=Fun f ts \<and> f\<notin>C)"

definition checkpoint_skeleton_safe :: "'f set \<Rightarrow> ('f,'v) trs \<Rightarrow> bool" where
 "checkpoint_skeleton_safe C R =
    (\<forall>(l,r)\<in>R. checkpoint_opaque_root C l \<and> checkpoint_opaque_root C r)"

lemma checkpoint_opaque_instance:
 "checkpoint_opaque_root C t \<Longrightarrow> checkpoint_skeleton C (t \<cdot> sigma) = Var ()"
 by (auto simp: checkpoint_opaque_root_def)

lemma checkpoint_skeleton_context:
 assumes "checkpoint_skeleton C s = checkpoint_skeleton C t"
 shows "checkpoint_skeleton C (D\<langle>s\<rangle>) = checkpoint_skeleton C (D\<langle>t\<rangle>)"
 using assms by (induct D) auto

lemma checkpoint_skeleton_rstep:
 assumes safe: "checkpoint_skeleton_safe C R"
 and step: "(s,t)\<in>rstep R"
 shows "checkpoint_skeleton C s = checkpoint_skeleton C t"
proof -
 obtain l r D sigma where rule: "(l,r)\<in>R"
   and s: "s=D\<langle>l\<cdot>sigma\<rangle>" and t: "t=D\<langle>r\<cdot>sigma\<rangle>"
   using step by auto
 have lhs: "checkpoint_opaque_root C l" and rhs: "checkpoint_opaque_root C r"
   using safe rule unfolding checkpoint_skeleton_safe_def by auto
 have "checkpoint_skeleton C (l\<cdot>sigma) = checkpoint_skeleton C (r\<cdot>sigma)"
   using lhs rhs by (auto simp: checkpoint_opaque_root_def)
 then show ?thesis unfolding s t by (rule checkpoint_skeleton_context)
qed

lemma checkpoint_skeleton_rsteps:
 assumes safe: "checkpoint_skeleton_safe C R"
 and steps: "(s,t)\<in>(rstep R)\<^sup>*"
 shows "checkpoint_skeleton C s = checkpoint_skeleton C t"
 using steps by (induct rule: rtrancl_induct)
   (auto dest: checkpoint_skeleton_rstep[OF safe])

lemma checkpoint_skeleton_measure_invariant:
 assumes "checkpoint_skeleton_safe C R" "(s,t)\<in>(rstep R)\<^sup>*"
 shows "measure_tree (checkpoint_skeleton C s) = measure_tree (checkpoint_skeleton C t)"
 using checkpoint_skeleton_rsteps[OF assms] by simp

fun checkpoint_skeleton_safe_rule where
 "checkpoint_skeleton_safe_rule C (Fun f ss,Fun g ts) = (f\<notin>C \<and> g\<notin>C)"
| "checkpoint_skeleton_safe_rule C _ = False"

lemma checkpoint_skeleton_safe_rule_correct:
 "checkpoint_skeleton_safe_rule C (l,r) =
   (checkpoint_opaque_root C l \<and> checkpoint_opaque_root C r)"
 by (cases l; cases r) (auto simp: checkpoint_opaque_root_def)

lemma checkpoint_skeleton_safe_list:
 "list_all (checkpoint_skeleton_safe_rule C) rules = checkpoint_skeleton_safe C (set rules)"
 by (auto simp: checkpoint_skeleton_safe_def list_all_iff checkpoint_skeleton_safe_rule_correct)

text \<open>Control roots need only be excluded from support left-hand sides.
This weaker condition is separate from constructor-skeleton preservation.\<close>

lemma checkpoint_control_root_step:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and step: "(Fun f ss,t)\<in>rstep R"
 shows "\<exists>ts. t=Fun f ts"
proof -
 obtain l r D sigma where rule: "(l,r)\<in>R"
  and source: "Fun f ss=D\<langle>l\<cdot>sigma\<rangle>"
  and target: "t=D\<langle>r\<cdot>sigma\<rangle>" using step by auto
 have opaque: "checkpoint_opaque_root K l" by (rule rules[OF rule])
 show ?thesis using source target opaque marked
  by (cases D) (auto simp: checkpoint_opaque_root_def)
qed

lemma checkpoint_control_root_steps:
 assumes rules: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root K l"
 and marked: "f\<in>K" and steps: "(Fun f ss,t)\<in>(rstep R)\<^sup>*"
 shows "\<exists>ts. t=Fun f ts"
 using steps
proof (induct rule: rtrancl_induct)
 case base show ?case by auto
next
 case (step y z)
 obtain ts where y: "y=Fun f ts" using step.hyps(3) by blast
 show ?case by (rule checkpoint_control_root_step[OF rules marked step.hyps(2)[unfolded y]])
qed

text \<open>Both exclusions are necessary even for a one-step observation.\<close>
lemma checkpoint_collapsing_counterexample:
 fixes c f :: 'f
 assumes "c\<in>C" "f\<notin>C"
 shows "(Fun f [Fun c []],Fun c [])\<in>rstep {(Fun f [Var ()],Var ())}"
   "checkpoint_skeleton C (Fun f [Fun c []]) \<noteq> checkpoint_skeleton C (Fun c [])"
proof -
 show "(Fun f [Fun c []],Fun c [])\<in>rstep {(Fun f [Var ()],Var ())}"
   by (rule rstep.rstep[where C=Hole and \<sigma>="\<lambda>_. Fun c []"]) auto
 show "checkpoint_skeleton C (Fun f [Fun c []]) \<noteq> checkpoint_skeleton C (Fun c [])"
   using assms by simp
qed

lemma checkpoint_constructor_producer_rejected:
 "c\<in>C \<Longrightarrow> \<not> checkpoint_skeleton_safe_rule C (Fun f ts, Fun c us)"
 by simp

lemma checkpoint_constructor_rewriter_rejected:
 "c\<in>C \<Longrightarrow> \<not> checkpoint_skeleton_safe_rule C (Fun c ts, Fun f us)"
 by simp

ML \<open>
val checked = @{thms checkpoint_skeleton_context checkpoint_skeleton_rstep
 checkpoint_skeleton_rsteps checkpoint_skeleton_measure_invariant
 checkpoint_skeleton_safe_rule_correct checkpoint_skeleton_safe_list
 checkpoint_collapsing_counterexample checkpoint_constructor_producer_rejected
 checkpoint_constructor_rewriter_rejected checkpoint_control_root_step checkpoint_control_root_steps};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checkpoint skeleton proof" else ();
\<close>
end
