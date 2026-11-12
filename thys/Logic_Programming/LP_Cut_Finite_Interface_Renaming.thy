theory LP_Cut_Finite_Interface_Renaming
 imports LP_Cut_MGU_Fresh_Support
begin

text \<open>A finite private namespace can be exchanged with fresh names while
fixing every variable outside the two supports. This is a bijection, so it
preserves sharing rather than projecting private variables away.\<close>

definition lpc_exchange_support where
 "lpc_exchange_support B q x =
   (if x \<in> B then q x else if x \<in> q ` B then inv_into B q x else x)"

lemma lpc_exchange_support_involution:
 assumes injective: "inj_on q B" and disjoint: "B \<inter> q ` B = {}"
 shows "lpc_exchange_support B q (lpc_exchange_support B q x) = x"
proof (cases "x \<in> B")
 case True
 have outside: "q x \<notin> B" using disjoint True by blast
 show ?thesis using True outside inv_into_f_f[OF injective True]
   by (simp add: lpc_exchange_support_def)
next
 case False
 show ?thesis
 proof (cases "x \<in> q ` B")
  case True
  then obtain y where y: "y \<in> B" "x = q y" by blast
  have inverse: "inv_into B q x = y" using y inv_into_f_f[OF injective] by simp
  show ?thesis using False True y inverse by (simp add: lpc_exchange_support_def)
 next
  case False
  with \<open>x \<notin> B\<close> show ?thesis by (simp add: lpc_exchange_support_def)
 qed
qed

lemma lpc_exchange_support_bij:
 assumes "inj_on q B" "B \<inter> q ` B = {}"
 shows "bij (lpc_exchange_support B q)"
proof -
 have twice: "\<And>x. lpc_exchange_support B q (lpc_exchange_support B q x) = x"
   using lpc_exchange_support_involution[OF assms] .
 show ?thesis unfolding bij_def inj_on_def surj_def using twice by metis
qed

lemma lpc_exchange_support_fixes_interface:
 assumes "A \<inter> B = {}" "A \<inter> q ` B = {}" "x \<in> A"
 shows "lpc_exchange_support B q x = x"
 using assms by (auto simp: lpc_exchange_support_def)

lemma lpc_fresh_private_involution:
 fixes A B C :: "string set"
 assumes "finite A" "finite B" "finite C" "A \<inter> B = {}"
 shows "\<exists>p. (\<forall>x. p (p x) = x) \<and> bij p \<and> (\<forall>x\<in>A. p x = x) \<and> p ` B \<inter> (A \<union> B \<union> C) = {}"
proof -
 obtain q :: "string \<Rightarrow> string" where q:
   "inj q" "(A \<union> B \<union> C) \<inter> range q = {}"
   using lpc_fresh_namespace_for_finite_interface[of "A \<union> B \<union> C"] assms by auto
 have inj: "inj_on q B" using q(1) by (auto simp: inj_on_def)
 have disjoint: "B \<inter> q ` B = {}" using q(2) by blast
 have inverse: "\<forall>x. lpc_exchange_support B q (lpc_exchange_support B q x) = x"
   using lpc_exchange_support_involution[OF inj disjoint] by blast
 have bij: "bij (lpc_exchange_support B q)"
   by (rule lpc_exchange_support_bij[OF inj disjoint])
 have fixed: "\<forall>x\<in>A. lpc_exchange_support B q x = x"
   using assms(4) q(2) by (auto simp: lpc_exchange_support_def)
 have moved: "lpc_exchange_support B q ` B = q ` B"
   by (auto simp: lpc_exchange_support_def)
 show ?thesis
   by (rule exI[of _ "lpc_exchange_support B q"])
     (use inverse bij fixed moved q(2) in blast)
qed

lemma lpc_fresh_private_permutation:
 fixes A B C :: "string set"
 assumes "finite A" "finite B" "finite C" "A \<inter> B = {}"
 shows "\<exists>p. bij p \<and> (\<forall>x\<in>A. p x = x) \<and> p ` B \<inter> (A \<union> B \<union> C) = {}"
 using lpc_fresh_private_involution[OF assms] by blast

ML \<open>
val checked = [@{thm lpc_exchange_support_involution},
 @{thm lpc_exchange_support_bij}, @{thm lpc_fresh_private_permutation}, @{thm lpc_fresh_private_involution}, @{thm lpc_exchange_support_fixes_interface}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite interface renaming dependency" else ();
\<close>
end
