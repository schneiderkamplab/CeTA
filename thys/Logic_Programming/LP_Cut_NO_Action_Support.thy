theory LP_Cut_NO_Action_Support
 imports LP_Cut_NO_Renamed_Control LP_Cut_NO_Return_Trace
begin

definition lpc_no_program_vars where
 "lpc_no_program_vars P = (\<Union>c\<in>set P.
   vars_term (fst c) \<union> (\<Union>g\<in>set (snd c). \<Union>t\<in>set (lp_cut_terms g). vars_term t))"

lemma lpc_no_program_vars_finite[simp]:
 "finite (lpc_no_program_vars P)"
 by (simp add: lpc_no_program_vars_def)

lemma lpc_no_program_head_vars:
 "c<length P \<Longrightarrow> vars_term (fst (P!c)) \<subseteq> lpc_no_program_vars P"
 using nth_mem[of c P] by (fastforce simp: lpc_no_program_vars_def)

lemma lpc_no_program_body_vars:
 "c<length P \<Longrightarrow>
   \<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> lpc_no_program_vars P"
 using nth_mem[of c P] by (fastforce simp: lpc_no_program_vars_def)

fun lpc_no_action_support where
 "lpc_no_action_support P (LPCNOResolve k V images) = set V \<union> lp_prefix k ` lpc_no_program_vars P"
| "lpc_no_action_support P (LPCNOResolveSwap k V images x y) =
    (set V \<union> {x,y}) \<union> lp_prefix k ` lpc_no_program_vars P"
| "lpc_no_action_support P (LPCNOUnify V images) = set V"
| "lpc_no_action_support P action = {}"

lemma lpc_no_action_support_finite[simp]:
 "finite (lpc_no_action_support P action)"
 by (cases action) simp_all

definition lpc_no_return_rename_safe where
 "lpc_no_return_rename_safe P p extra action =
   ((\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpc_no_action_support P action = {})"

lemma lpc_no_return_rename_safe_subset:
 assumes safe: "lpc_no_return_rename_safe P p extra action"
   and subset: "S \<subseteq> lpc_no_action_support P action"
   and member: "z\<in>\<Union>(vars_term ` set extra)"
 shows "z\<notin>p ` S"
 using assms by (auto simp: lpc_no_return_rename_safe_def)

lemma lpc_no_return_rename_safe_fresh:
 assumes safe: "lpc_no_return_rename_safe P p extra action"
   and subset: "lp_prefix k ` B \<subseteq> lpc_no_action_support P action"
   and member: "t\<in>set extra"
 shows "vars_term t \<inter> (p \<circ> lp_prefix k) ` B = {}"
 using assms by (auto simp: lpc_no_return_rename_safe_def o_def)

lemma lpc_no_uniform_trace_renaming:
 fixes A C :: "string set"
 assumes finite: "finite A" "finite C"
   and separate: "A \<inter> C = {}"
 shows "\<exists>p. (\<forall>z. p (p z) = z) \<and> (\<forall>z\<in>A. p z = z) \<and>
   (\<forall>action\<in>set actions. \<forall>extra.
     (\<Union>t\<in>set extra. vars_term t) \<subseteq> C \<longrightarrow>
       lpc_no_return_rename_safe P p extra action)"
proof -
 let ?S = "\<Union>action\<in>set actions. lpc_no_action_support P action"
 have finite_support: "finite ?S" by simp
 have private_finite: "finite (?S-A)" using finite_support by simp
 have private_disjoint: "A \<inter> (?S-A) = {}" by blast
 obtain p :: "string \<Rightarrow> string" where inverse: "\<forall>z. p (p z) = z"
   and fixed: "\<forall>z\<in>A. p z = z"
   and moved: "p ` (?S-A) \<inter> (A \<union> (?S-A) \<union> C) = {}"
   using lpc_fresh_private_involution[OF finite(1) private_finite finite(2) private_disjoint]
   by (elim exE conjE) assumption
 have outside: "p z\<notin>C" if member: "z\<in>?S" for z
 proof (cases "z\<in>A")
   case True
   have equal: "p z = z" using fixed True by blast
   show ?thesis using separate True by (auto simp: equal)
 next
   case False
   have member_private: "z\<in>?S-A" using member False by simp
   have image: "p z\<in>p ` (?S-A)" by (rule imageI[OF member_private])
   show ?thesis using moved image by blast
 qed
 have safe: "lpc_no_return_rename_safe P p extra action"
   if action: "action\<in>set actions" and extra: "(\<Union>t\<in>set extra. vars_term t) \<subseteq> C"
   for action extra
 proof -
   have included: "lpc_no_action_support P action \<subseteq> ?S" using action by blast
   have disjoint: "p ` lpc_no_action_support P action \<inter> C = {}"
   proof (rule equals0I)
     fix z assume member: "z\<in>p ` lpc_no_action_support P action \<inter> C"
     then obtain w where w: "w\<in>lpc_no_action_support P action" "z = p w" by auto
     have supported: "w\<in>?S" using included w(1) by blast
     show False using outside[OF supported] member w(2) by simp
   qed
   show ?thesis using disjoint extra by (auto simp: lpc_no_return_rename_safe_def)
 qed
 show ?thesis
 proof (rule exI[of _ p], intro conjI)
   show "\<forall>z. p (p z) = z" by (rule inverse)
   show "\<forall>z\<in>A. p z = z" by (rule fixed)
   show "\<forall>action\<in>set actions. \<forall>extra.
     (\<Union>t\<in>set extra. vars_term t) \<subseteq> C \<longrightarrow>
       lpc_no_return_rename_safe P p extra action"
     by (intro ballI allI impI, rule safe; assumption)
 qed
qed

ML \<open>
val checked = [@{thm lpc_no_action_support_finite}, @{thm lpc_no_program_head_vars},
 @{thm lpc_no_uniform_trace_renaming}, @{thm lpc_no_program_body_vars}, @{thm lpc_no_return_rename_safe_subset}, @{thm lpc_no_return_rename_safe_fresh}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite NO action support" else ();
\<close>
end
