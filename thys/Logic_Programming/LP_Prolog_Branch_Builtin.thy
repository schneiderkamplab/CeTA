theory LP_Prolog_Branch_Builtin
 imports LP_Prolog_Return_Check
begin

text \<open>Finite source syntax is lowered into the existing cut-free goal
forms. In particular equality keeps its most-general substitution semantics.
Unsupported dynamic control remains outside this bridge's domain.\<close>
inductive lpp_branch_lower ::
  "(string lp_cut_symbol,string) lp_iterm \<Rightarrow>
   (string lp_cut_symbol,string) lp_iterm lp_cut_goal list \<Rightarrow> bool" where
  atom: "lpp_branch_lower (LPIFun (LPCUser f) ts) [LPCAtom (LPIFun (LPCUser f) ts)]"
| conjunction: "lpp_branch_lower a aa \<Longrightarrow> lpp_branch_lower b bb \<Longrightarrow>
    lpp_branch_lower (LPIFun LPCComma [a,b]) (aa@bb)"
| unify: "lpp_branch_lower (LPIFun LPCEquals [a,b]) [LPCUnify a b]"
| truth: "lpp_branch_lower (LPIFun LPCTruth []) [LPCTrue]"
| fail: "lpp_branch_lower (LPIFun LPCFailure []) [LPCFail]"

lemma lpp_branch_lower_plain:
  "lpp_branch_lower a gs \<Longrightarrow> list_all lpp_plain_goal gs"
  by (induction rule: lpp_branch_lower.induct) auto

lemma lpp_branch_lower_unique:
  assumes "lpp_branch_lower a gs" "lpp_branch_lower a hs"
  shows "gs=hs"
  using assms
proof (induction arbitrary: hs rule: lpp_branch_lower.induct)
  case (atom f ts)
  from atom.prems show ?case by (cases (no_simp) rule: lpp_branch_lower.cases) simp_all
next
  case (conjunction a aa b bb)
  from conjunction.prems show ?case
    by (cases (no_simp) rule: lpp_branch_lower.cases) (simp_all add: conjunction.IH)
next
  case (unify a b)
  from unify.prems show ?case
    apply (cases (no_simp) rule: lpp_branch_lower.cases)
    by simp_all
next
  case truth
  from truth.prems show ?case by (cases (no_simp) rule: lpp_branch_lower.cases) simp_all
next
  case fail
  from fail.prems show ?case by (cases (no_simp) rule: lpp_branch_lower.cases) simp_all
qed

fun lpp_branch_lower_term :: "string lpc_term \<Rightarrow> string lpc_term lp_cut_goal list option" where
  "lpp_branch_lower_term (Fun (LPCUser f) ts) = Some [LPCAtom (Fun (LPCUser f) ts)]"
| "lpp_branch_lower_term (Fun LPCComma [a,b]) =
    (case (lpp_branch_lower_term a,lpp_branch_lower_term b) of
      (Some aa,Some bb) \<Rightarrow> Some (aa@bb) | _ \<Rightarrow> None)"
| "lpp_branch_lower_term (Fun LPCEquals [a,b]) = Some [LPCUnify a b]"
| "lpp_branch_lower_term (Fun LPCTruth []) = Some [LPCTrue]"
| "lpp_branch_lower_term (Fun LPCFailure []) = Some [LPCFail]"
| "lpp_branch_lower_term _ = None"

lemma lpp_branch_lower_term_sound:
  "lpp_branch_lower_term a=Some gs \<Longrightarrow>
    lpp_branch_lower (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  apply (induction a arbitrary: gs rule: lpp_branch_lower_term.induct)
  apply (auto simp: lpp_branch_lower_term.simps split: if_splits list.splits option.splits prod.splits intro: lpp_branch_lower.intros)
  done

definition lpp_choice_left where
  "lpp_choice_left a = (case a of LPIFun f ts \<Rightarrow>
    f\<noteq>LPCUser ''2:->'' \<or> length ts\<noteq>2 | _ \<Rightarrow> False)"

lemma lpp_choice_left_Fun[simp]:
  "lpp_choice_left (LPIFun f ts) = (f\<noteq>LPCUser ''2:->'' \<or> length ts\<noteq>2)"
  by (simp add: lpp_choice_left_def)

lemma lpp_choice_left_subst:
  "lpp_choice_left a \<Longrightarrow> lpp_choice_left (lp_isubst a sigma)"
  by (cases a) (auto simp: lpp_choice_left_def)

definition lpp_branch_outcome where
  "lpp_branch_outcome ts outcome = ((\<exists>c y n cs ys ns.
    ts=[LPIFun (LPCUser ''2:->'') [c,y],n] \<and>
    lpp_branch_lower c cs \<and> lpp_branch_lower y ys \<and> lpp_branch_lower n ns \<and>
    outcome=LPPBuiltinBranch cs ys ns) \<or>
    (\<exists>a b left right. ts=[a,b] \<and> lpp_choice_left a \<and>
      lpp_branch_lower a left \<and> lpp_branch_lower b right \<and>
      outcome=LPPBuiltinChoice left right))"

definition lpp_branch_domain where
  "lpp_branch_domain ts = (\<exists>outcome. lpp_branch_outcome ts outcome)"

lemma lpp_branch_outcome_arity:
  "lpp_branch_outcome ts outcome \<Longrightarrow> length ts=2"
  by (auto simp: lpp_branch_outcome_def)

end
