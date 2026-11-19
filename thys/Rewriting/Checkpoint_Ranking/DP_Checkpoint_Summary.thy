theory DP_Checkpoint_Summary
 imports DP_Checkpoint_Skeleton
begin

text \<open>A successful-relation summary assigns each residual term a set of
possible observations. Support rewriting may only remove possibilities. Inputs
may contain arbitrary forged outputs as data: only constructor skeletons are
observed in data coordinates, while active subcalls use the set interpretation.
Thus an input need not satisfy an invariant on all of its subterms.\<close>

fun checkpoint_interpret :: "'f set \<Rightarrow>
 ('f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set) \<Rightarrow>
 ('f,'v) term \<Rightarrow> 'a set" where
 "checkpoint_interpret C A (Var x) = UNIV"
| "checkpoint_interpret C A (Fun f ts) =
 A f (map (checkpoint_skeleton C) ts) (map (checkpoint_interpret C A) ts)"

definition checkpoint_algebra_mono where
 "checkpoint_algebra_mono A = (\<forall>f shapes xs ys.
   list_all2 (\<subseteq>) xs ys \<longrightarrow> A f shapes xs \<subseteq> A f shapes ys)"

lemma checkpoint_interpret_context:
 fixes s t :: "('f,'v) term" and D :: "('f,'v) ctxt"
 and A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 assumes mono: "checkpoint_algebra_mono A"
 and skeleton: "checkpoint_skeleton C s = checkpoint_skeleton C t"
 and included: "checkpoint_interpret C A t \<subseteq> checkpoint_interpret C A s"
 shows "checkpoint_interpret C A (D\<langle>t\<rangle>) \<subseteq> checkpoint_interpret C A (D\<langle>s\<rangle>)"
proof (induct D)
 case Hole show ?case using included by simp
next
 case (More f ss D ts)
 have shape: "checkpoint_skeleton C (D\<langle>s\<rangle>) = checkpoint_skeleton C (D\<langle>t\<rangle>)"
  by (rule checkpoint_skeleton_context[OF skeleton])
 have children: "list_all2 (\<subseteq>)
   (map (checkpoint_interpret C A) ss @ checkpoint_interpret C A (D\<langle>t\<rangle>) # map (checkpoint_interpret C A) ts)
   (map (checkpoint_interpret C A) ss @ checkpoint_interpret C A (D\<langle>s\<rangle>) # map (checkpoint_interpret C A) ts)"
  using More by (simp add: list_all2_append list_all2_same)
 show ?case using mono children
  unfolding checkpoint_algebra_mono_def by (simp add: shape)
qed

lemma checkpoint_interpret_rstep:
 fixes R :: "('f,'v) trs"
 and A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 assumes safe: "checkpoint_skeleton_safe C R"
 and mono: "checkpoint_algebra_mono A"
 and rules: "\<And>l r sigma. (l,r)\<in>R \<Longrightarrow>
   checkpoint_interpret C A (r\<cdot>sigma) \<subseteq> checkpoint_interpret C A (l\<cdot>(sigma::'v \<Rightarrow> ('f,'v) term))"
 and step: "(s,t)\<in>rstep R"
 shows "checkpoint_interpret C A t \<subseteq> checkpoint_interpret C A s"
proof -
 obtain l r D sigma where rule: "(l,r)\<in>R"
  and s: "s=D\<langle>l\<cdot>sigma\<rangle>" and t: "t=D\<langle>r\<cdot>sigma\<rangle>"
  using step by auto
 have shape: "checkpoint_skeleton C (l\<cdot>sigma) = checkpoint_skeleton C (r\<cdot>sigma)"
  using safe rule by (auto simp: checkpoint_skeleton_safe_def checkpoint_opaque_root_def)
 show ?thesis unfolding s t
  by (rule checkpoint_interpret_context[OF mono shape], rule rules[OF rule])
qed

lemma checkpoint_interpret_rsteps:
 fixes R :: "('f,'v) trs"
 and A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 assumes safe: "checkpoint_skeleton_safe C R"
 and mono: "checkpoint_algebra_mono A"
 and rules: "\<And>l r sigma. (l,r)\<in>R \<Longrightarrow>
   checkpoint_interpret C A (r\<cdot>sigma) \<subseteq> checkpoint_interpret C A (l\<cdot>(sigma::'v \<Rightarrow> ('f,'v) term))"
 and steps: "(s,t)\<in>(rstep R)\<^sup>*"
 shows "checkpoint_interpret C A t \<subseteq> checkpoint_interpret C A s"
 using steps
proof (induct rule: rtrancl_induct)
 case base show ?case by simp
next
 case (step y z)
 have "checkpoint_interpret C A z \<subseteq> checkpoint_interpret C A y"
  by (rule checkpoint_interpret_rstep[OF safe mono rules step.hyps(2)])
 then show ?case using step.hyps(3) by blast
qed

lemma checkpoint_success_inversion:
 fixes R :: "('f,'v) trs"
 and A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 assumes safe: "checkpoint_skeleton_safe C R"
 and mono: "checkpoint_algebra_mono A"
 and rules: "\<And>l r sigma. (l,r)\<in>R \<Longrightarrow>
   checkpoint_interpret C A (r\<cdot>sigma) \<subseteq> checkpoint_interpret C A (l\<cdot>(sigma::'v \<Rightarrow> ('f,'v) term))"
 and success: "(input,output)\<in>(rstep R)\<^sup>*"
 and observed: "result\<in>checkpoint_interpret C A output"
 shows "result\<in>checkpoint_interpret C A input"
 using checkpoint_interpret_rsteps[OF safe mono rules success] observed by blast

lemma checkpoint_closed_skeleton_exact:
 assumes closed: "vars_term (checkpoint_skeleton C t)={}"
 shows "vars_term t={} \<and> funs_term t=funs_term (checkpoint_skeleton C t)"
 using closed
 by (induct t) (auto split: if_splits)

ML \<open>
val checked = @{thms checkpoint_interpret_context checkpoint_interpret_rstep
 checkpoint_interpret_rsteps checkpoint_success_inversion checkpoint_closed_skeleton_exact};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted residual summary inversion" else ();
\<close>
end
