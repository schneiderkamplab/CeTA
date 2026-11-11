theory LP_Prolog_Control_Return_Model
 imports LP_Prolog_Inline_Return_Model LP_Prolog_Branch_Builtin LP_Prolog_Finite_Source
begin

text \<open>This is a model of successful answers, not a second execution
semantics. Conditional alternatives are interpreted separately. In particular,
the else alternative assumes no successful facts about the condition. Finite
model derivations do not assert termination or finite runtime terms.\<close>

lemma lpp_control_model_goal_mono[mono]:
  "(\<And>t. A t \<longrightarrow> B t) \<Longrightarrow> lpc_model_goal A g \<longrightarrow> lpc_model_goal B g"
  by (cases g) auto

inductive lpp_control_return_model ::
  "((string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool) \<Rightarrow>
   (string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  for M where
  ordinary: "f\<noteq>''2:;'' \<Longrightarrow> f\<noteq>''3:subtract'' \<Longrightarrow>
    M (LPIFun (LPCUser f) ts) \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser f) ts)"
| conditional_yes: "lpp_branch_lower c cs \<Longrightarrow> lpp_branch_lower y ys \<Longrightarrow>
    lpp_branch_lower n ns \<Longrightarrow>
    list_all (lpc_model_goal (lpp_control_return_model M)) (cs@ys) \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser ''2:;'') [LPIFun (LPCUser ''2:->'') [c,y],n])"
| conditional_no: "lpp_branch_lower c cs \<Longrightarrow> lpp_branch_lower y ys \<Longrightarrow>
    lpp_branch_lower n ns \<Longrightarrow>
    list_all (lpc_model_goal (lpp_control_return_model M)) ns \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser ''2:;'') [LPIFun (LPCUser ''2:->'') [c,y],n])"
| choice: "lpp_choice_left a \<Longrightarrow>
    lpp_branch_lower a left \<Longrightarrow> lpp_branch_lower b right \<Longrightarrow>
    (list_all (lpc_model_goal (lpp_control_return_model M)) left \<or>
     list_all (lpc_model_goal (lpp_control_return_model M)) right) \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser ''2:;'') [a,b])"
| subtract_call: "length ts=3 \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser lpp_subtract_library) ts) \<Longrightarrow>
    lpp_control_return_model M (LPIFun (LPCUser ''3:subtract'') ts)"

lemma lpp_control_return_ordinary:
  assumes "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
  shows "lpp_control_return_model M (LPIFun (LPCUser f) ts) =
    M (LPIFun (LPCUser f) ts)"
proof
  assume model: "lpp_control_return_model M (LPIFun (LPCUser f) ts)"
  from model show "M (LPIFun (LPCUser f) ts)"
    by (cases (no_simp) rule: lpp_control_return_model.cases) (use assms in simp_all)
next
  assume "M (LPIFun (LPCUser f) ts)"
  then show "lpp_control_return_model M (LPIFun (LPCUser f) ts)"
    by (rule lpp_control_return_model.ordinary[OF assms])
qed

lemma lpp_branch_lower_subst:
  "lpp_branch_lower a gs \<Longrightarrow>
    lpp_branch_lower (lp_isubst a sigma) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) gs)"
proof (induction rule: lpp_branch_lower.induct)
  case (atom f ts)
  show ?case unfolding lp_isubst_Fun list.map lp_cut_map.simps
    by (rule lpp_branch_lower.atom)
next
  case (conjunction a aa b bb)
  show ?case unfolding lp_isubst_Fun list.map map_append
    by (rule lpp_branch_lower.conjunction[OF conjunction.IH])
next
  case (unify a b)
  show ?case unfolding lp_isubst_Fun list.map lp_cut_map.simps
    by (rule lpp_branch_lower.unify)
next
  case truth
  show ?case unfolding lp_isubst_Fun list.map lp_cut_map.simps
    by (rule lpp_branch_lower.truth)
next
  case fail
  show ?case unfolding lp_isubst_Fun list.map lp_cut_map.simps
    by (rule lpp_branch_lower.fail)
qed

lemma lpp_control_goal_subst:
  "lpc_model_goal (\<lambda>t. M t \<and> M (lp_isubst t sigma)) g \<Longrightarrow>
    lpc_model_goal M (lp_cut_map (\<lambda>t. lp_isubst t sigma) g)"
  by (cases g) auto

lemma lpp_control_return_subst:
  assumes stable: "\<And>t sigma. M t \<Longrightarrow> M (lp_isubst t sigma)"
    and known: "lpp_control_return_model M t"
  shows "lpp_control_return_model M (lp_isubst t sigma)"
  using known
proof (induction rule: lpp_control_return_model.induct)
  case (ordinary f ts)
  have model: "M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    by (rule stable[OF ordinary.hyps(3)])
  show ?case unfolding lp_isubst_Fun
    by (rule lpp_control_return_model.ordinary[OF ordinary.hyps(1,2)]) (use model in simp)
next
  case (conditional_yes c cs y ys n ns)
  have body: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys))"
    using conditional_yes by (auto simp: list_all_iff intro: lpp_control_goal_subst)
  have "lpp_control_return_model M (LPIFun (LPCUser ''2:;'')
      [LPIFun (LPCUser ''2:->'') [lp_isubst c sigma,lp_isubst y sigma],lp_isubst n sigma])"
    by (rule lpp_control_return_model.conditional_yes[OF
      lpp_branch_lower_subst[OF conditional_yes.hyps(1)]
      lpp_branch_lower_subst[OF conditional_yes.hyps(2)]
      lpp_branch_lower_subst[OF conditional_yes.hyps(3)]]) (use body in simp)
  then show ?case by simp
next
  case (conditional_no c cs y ys n ns)
  have body: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
    using conditional_no by (auto simp: list_all_iff intro: lpp_control_goal_subst)
  have "lpp_control_return_model M (LPIFun (LPCUser ''2:;'')
      [LPIFun (LPCUser ''2:->'') [lp_isubst c sigma,lp_isubst y sigma],lp_isubst n sigma])"
    by (rule lpp_control_return_model.conditional_no[OF
      lpp_branch_lower_subst[OF conditional_no.hyps(1)]
      lpp_branch_lower_subst[OF conditional_no.hyps(2)]
      lpp_branch_lower_subst[OF conditional_no.hyps(3)]]) (rule body)
  then show ?case by simp
next
  case (choice a left b right)
  have alternatives: "list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) left) \<or>
    list_all (lpc_model_goal (lpp_control_return_model M))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) right)"
    using choice by (auto simp: list_all_iff intro: lpp_control_goal_subst)
  show ?case unfolding lp_isubst_Fun list.map
    by (rule lpp_control_return_model.choice[OF lpp_choice_left_subst[OF choice.hyps(1)]
      lpp_branch_lower_subst[OF choice.hyps(2)] lpp_branch_lower_subst[OF choice.hyps(3)] alternatives])
next
  case (subtract_call ts)
  show ?case unfolding lp_isubst_Fun
    by (rule lpp_control_return_model.subtract_call) (use subtract_call in simp_all)
qed

lemma lpp_control_return_conditional:
  assumes lower: "lpp_branch_lower c cs" "lpp_branch_lower y ys" "lpp_branch_lower n ns"
    and model: "lpp_control_return_model M
      (LPIFun (LPCUser ''2:;'') [LPIFun (LPCUser ''2:->'') [c,y],n])"
  shows "list_all (lpc_model_goal (lpp_control_return_model M)) (cs@ys) \<or>
    list_all (lpc_model_goal (lpp_control_return_model M)) ns"
  using model
  by (cases (no_simp) rule: lpp_control_return_model.cases)
    (use lower in \<open>auto dest: lpp_branch_lower_unique\<close>)

lemma lpp_control_return_choice:
  assumes left: "lpp_choice_left a"
    and lower: "lpp_branch_lower a aa" "lpp_branch_lower b bb"
    and model: "lpp_control_return_model M (LPIFun (LPCUser ''2:;'') [a,b])"
  shows "list_all (lpc_model_goal (lpp_control_return_model M)) aa \<or>
    list_all (lpc_model_goal (lpp_control_return_model M)) bb"
  using model
  by (cases (no_simp) rule: lpp_control_return_model.cases)
    (use left lower in \<open>auto dest: lpp_branch_lower_unique\<close>)

lemma lpp_control_return_delegate:
  assumes "lpp_control_return_model M (LPIFun (LPCUser ''3:subtract'') ts)"
  shows "lpp_control_return_model M (LPIFun (LPCUser lpp_subtract_library) ts)"
  using assms by (cases (no_simp) rule: lpp_control_return_model.cases) auto

ML \<open>
val checked = [@{thm lpp_control_return_ordinary}, @{thm lpp_branch_lower_subst},
  @{thm lpp_control_return_subst}, @{thm lpp_control_return_conditional},
  @{thm lpp_control_return_delegate}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control return model" else ();
\<close>

end
