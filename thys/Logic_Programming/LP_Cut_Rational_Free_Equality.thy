theory LP_Cut_Rational_Free_Equality
 imports LP_Cut_MGU_Coverage LP_Cut_Table_Equality
begin

text \<open>A free runtime variable can be unified with any rational tree,
including a tree containing that same variable. The solution is a possibly
infinite tree; this theorem establishes no finite structural measure.\<close>

primcorec lpc_rational_bind ::
  "'v \<Rightarrow> 'f \<Rightarrow> ('f,'v) lp_iterm list \<Rightarrow> ('f,'v) lp_iterm \<Rightarrow> ('f,'v) lp_iterm" where
  "lpc_rational_bind x f roots t = (case t of
    LPIVar y \<Rightarrow> (if x=y then LPIFun f (map (lpc_rational_bind x f roots) roots) else LPIVar y)
  | LPIFun g children \<Rightarrow> LPIFun g (map (lpc_rational_bind x f roots) children))"

lemma lpc_rational_bind_var[simp]:
  "lpc_rational_bind x f roots (LPIVar y) =
    (if x=y then LPIFun f (map (lpc_rational_bind x f roots) roots) else LPIVar y)"
  by (subst lpc_rational_bind.code) simp

lemma lpc_rational_bind_fun[simp]:
  "lpc_rational_bind x f roots (LPIFun g children) =
    LPIFun g (map (lpc_rational_bind x f roots) children)"
  by (subst lpc_rational_bind.code) simp

lemma lpc_rational_bind_substitution:
  "lp_isubst t (\<lambda>y. if x=y then LPIFun f (map (lpc_rational_bind x f roots) roots) else LPIVar y)
    = lpc_rational_bind x f roots t"
  by (coinduction arbitrary: t rule: lp_iterm.coinduct_strong)
    (auto simp: list_all2_conv_all_nth split: lp_iterm.splits)

theorem lpc_free_runtime_variable_unifies:
  fixes t :: "('f,'v) lp_iterm" and x :: "'v"
  shows "\<exists>sigma :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_isubst (LPIVar x) sigma = lp_isubst t sigma"
proof (cases t)
  case (LPIVar y)
  show ?thesis unfolding LPIVar
    by (rule exI[of _ "\<lambda>_. LPIVar y"]) simp
next
  case (LPIFun f roots)
  let ?sigma = "\<lambda>y. if x=y then LPIFun f (map (lpc_rational_bind x f roots) roots) else LPIVar y"
  show ?thesis unfolding LPIFun
    by (rule exI[of _ ?sigma]) (simp add: lpc_rational_bind_substitution)
qed

lemma lpc_free_template_variable_unifies:
  fixes eta :: "'a \<Rightarrow> ('f,'v) lp_iterm"
  assumes "x\<in>F" "lpc_free_knowledge F eta"
  shows "\<exists>sigma :: 'v \<Rightarrow> ('f,'v) lp_iterm. lp_isubst (lp_ieval (Var x) eta) sigma = lp_isubst (lp_ieval t eta) sigma"
proof -
  obtain y where variable: "eta x=LPIVar y"
    using assms by (auto simp: lpc_free_knowledge_def)
  show ?thesis using lpc_free_runtime_variable_unifies[of y "lp_ieval t eta"]
    by (simp add: variable)
qed

fun lpc_free_equality_operand where
  "lpc_free_equality_operand F (Var x) = (x\<in>set F)"
| "lpc_free_equality_operand F _ = False"

definition lpc_check_free_equality where
  "lpc_check_free_equality fuel F a b mode =
    (lp_cut_check_equality fuel a b mode \<or>
      (mode=LPCAlwaysSuccess \<and> (lpc_free_equality_operand F a \<or> lpc_free_equality_operand F b)))"

lemma lpc_free_equality_success:
  fixes eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes "lpc_check_free_equality fuel F a b LPCAlwaysSuccess"
    "lpc_free_knowledge (set F) eta"
  shows "\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
    lp_isubst (lp_ieval a eta) sigma=lp_isubst (lp_ieval b eta) sigma"
proof -
  have left: "lpc_free_equality_operand F a \<Longrightarrow> ?thesis"
    using lpc_free_template_variable_unifies[OF _ assms(2)] by (cases a) auto
  have right: "lpc_free_equality_operand F b \<Longrightarrow> ?thesis"
  proof -
    assume operand: "lpc_free_equality_operand F b"
    then obtain x where shape: "b=Var x" and member: "x\<in>set F" by (cases b) auto
    have "\<exists>sigma :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm.
      lp_isubst (lp_ieval b eta) sigma=lp_isubst (lp_ieval a eta) sigma"
      unfolding shape by (rule lpc_free_template_variable_unifies[OF member assms(2)])
    then show ?thesis by metis
  qed
  show ?thesis using assms(1) left right lp_cut_equality_success
    by (auto simp: lpc_check_free_equality_def)
qed

lemma lpc_free_equality_failure:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes "lpc_check_free_equality fuel F a b LPCAlwaysFailure"
  shows "\<not>(\<exists>sigma :: string \<Rightarrow> ('f,string) lp_iterm.
    lp_isubst (lp_ieval a eta) sigma=lp_isubst (lp_ieval b eta) sigma)"
  by (rule lp_cut_equality_failure) (use assms in \<open>auto simp: lpc_check_free_equality_def\<close>)


definition lpc_check_free_equality_node where
  "lpc_check_free_equality_node fuel P Q nds nd F a b gs es k l next mode yes no =
    (lpcn_state nd=LPCGoals (LPCUnify a b#gs)#es \<and>
     lpc_check_free_equality fuel F a b mode \<and>
     (mode\<noteq>LPCAlwaysFailure \<longrightarrow>
       lp_cut_check_unify fuel k l (lpcn_ground nd) (lpcn_guards nd) a b gs es next \<and>
       (\<forall>x\<in>set (lpcn_vars nd). length x<k) \<and>
       lpc_check_link fuel Q nds nd (LPCGoals next#es) (lpcn_ground nd)
         (lpcn_guards nd@lpc_negative_guards k (set (lpcn_ground nd)) (lpcn_guards nd)@[LPCEqGuard a b True])
         [(a\<cdot>lp_cut_refresh k (set (lpcn_ground nd)),b\<cdot>lp_cut_refresh k (set (lpcn_ground nd)))] yes) \<and>
     (mode\<noteq>LPCAlwaysSuccess \<longrightarrow>
       lpc_check_link fuel Q nds nd es (lpcn_ground nd)
         (lpcn_guards nd@[LPCEqGuard a b False]) [] no))"

end
