theory LP_Prolog_Inline_Return_Model
 imports LP_Prolog_Source_Return_Model LP_Prolog_Finite_Evaluation LP_Prolog_Operation_Context
begin

text \<open>Evaluation and integer tests contribute guards to actual successful
source clauses. The evaluation relation is a parameter: integer typing follows
only from its conditional contract, never from an arbitrary successful result.
All other calls remain model obligations.\<close>

fun lpp_inline_return_model where
  "lpp_inline_return_model SP E (LPIFun (LPCUser f) ts) =
    (if f=''2:is'' then length ts=2 \<and> E (ts!1) (ts!0)
     else if f=''1:integer'' then length ts=1 \<and> lpp_is_integer (ts!0)
     else lpp_guarded_success SP E (f,ts))"
| "lpp_inline_return_model SP E _ = False"

fun lpp_inline_return_calls :: "(string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> string lpp_success_atom list" where
  "lpp_inline_return_calls [] = []"
| "lpp_inline_return_calls (LPCAtom (Fun (LPCUser f) ts)#gs) =
    (if f=''2:is'' \<or> f=''1:integer'' then lpp_inline_return_calls gs
     else (f,ts)#lpp_inline_return_calls gs)"
| "lpp_inline_return_calls (g#gs) = lpp_inline_return_calls gs"

fun lpp_inline_return_guards :: "(string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> string lpp_success_guard list" where
  "lpp_inline_return_guards [] = []"
| "lpp_inline_return_guards (LPCAtom (Fun (LPCUser f) ts)#gs) =
    (if f=''2:is'' then LPPSEvaluates (ts!1) (ts!0)#lpp_inline_return_guards gs
     else if f=''1:integer'' then LPPSInteger (ts!0)#lpp_inline_return_guards gs
     else lpp_inline_return_guards gs)"
| "lpp_inline_return_guards (g#gs) = lpp_inline_return_guards gs"

lemma lpp_inline_return_body:
  assumes control: "list_all (lpc_return_control_goal F) gs"
    and model: "list_all (lpc_model_goal (lpp_inline_return_model SP E))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  shows "list_all (lpp_guarded_success SP E)
    (map (\<lambda>b. lpp_success_atom_eval b eta) (lpp_inline_return_calls gs)) \<and>
    list_all (lpp_success_guard_holds E eta) (lpp_inline_return_guards gs)"
  using control model
  by (induct gs) (auto simp: lpc_return_control_goal_iff lpc_control_goal_iff lpp_success_atom_eval_def)

lemma lpp_inline_return_clause:
  assumes head: "h=Fun (LPCUser f) ts"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and control: "list_all (lpc_return_control_goal F) gs"
    and clause: "((f,ts),lpp_inline_return_calls gs,lpp_inline_return_guards gs)\<in>set SP"
  shows "lpc_model_program [(h,gs)] (lpp_inline_return_model SP E)"
proof -
  have safe: "list_all lpc_model_safe_goal gs" by (rule lpp_source_return_safe[OF control])
  have closed: "lpp_inline_return_model SP E (lp_ieval h eta)"
    if model: "list_all (lpc_model_goal (lpp_inline_return_model SP E))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)" for eta m
  proof -
    have body: "list_all (lpp_guarded_success SP E)
      (map (\<lambda>b. lpp_success_atom_eval b eta) (lpp_inline_return_calls gs))"
      and guards: "list_all (lpp_success_guard_holds E eta) (lpp_inline_return_guards gs)"
      using lpp_inline_return_body[OF control model] by auto
    have success: "lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) eta)"
      by (rule lpp_guarded_success.clause[OF clause guards body])
    show ?thesis using success by (simp add: head ordinary lpp_success_atom_eval_def)
  qed
  show ?thesis using safe closed by (auto simp: lpc_model_program_def)
qed

definition lpp_inline_return_program_check :: "(string,string) lp_cut_program \<Rightarrow> string set \<Rightarrow> string lpp_success_clause list \<Rightarrow> bool" where
  "lpp_inline_return_program_check P F SP = (\<forall>c<length P. \<exists>f ts.
    fst (P!c)=Fun (LPCUser f) ts \<and> (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and>
      list_all (lpc_return_control_goal F) (snd (P!c)) \<and>
      ((f,ts),lpp_inline_return_calls (snd (P!c)),lpp_inline_return_guards (snd (P!c)))\<in>set SP))"

lemma lpp_inline_return_program_check_code[code]:
  "lpp_inline_return_program_check P F SP = list_all (\<lambda>c.
    case fst c of Fun (LPCUser f) ts \<Rightarrow>
      (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_inline_return_calls (snd c),lpp_inline_return_guards (snd c))\<in>set SP)
    | _ \<Rightarrow> False) P"
proof -
  have local: "(\<exists>f ts. fst c=Fun (LPCUser f) ts \<and>
      (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_inline_return_calls (snd c),lpp_inline_return_guards (snd c))\<in>set SP)) =
    (case fst c of Fun (LPCUser f) ts \<Rightarrow>
      (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_inline_return_calls (snd c),lpp_inline_return_guards (snd c))\<in>set SP) | _ \<Rightarrow> False)" for c
  proof (cases "fst c")
    case (Var x) then show ?thesis by simp
  next
    case (Fun g ts) then show ?thesis by (cases g) auto
  qed
  show ?thesis by (simp only: lpp_inline_return_program_check_def local; simp only: list_all_length)
qed

theorem lpp_inline_return_program_sound:
  assumes checked: "lpp_inline_return_program_check P F SP"
  shows "lpc_scoped_model_program P F (lpp_inline_return_model SP E)"
proof (unfold lpc_scoped_model_program_def, intro allI impI)
  fix c assume index: "c<length P"
  obtain f ts where head: "fst (P!c)=Fun (LPCUser f) ts"
    and selected: "f\<in>F \<Longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> list_all (lpc_return_control_goal F) (snd (P!c)) \<and>
      ((f,ts),lpp_inline_return_calls (snd (P!c)),lpp_inline_return_guards (snd (P!c)))\<in>set SP"
    using checked index by (auto simp: lpp_inline_return_program_check_def)
  have model: "lpc_model_program [P!c] (lpp_inline_return_model SP E)" if f: "f\<in>F"
  proof -
    have ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
      using selected[OF f] by auto
    have body: "list_all (lpc_return_control_goal F) (snd (P!c))"
      and clause: "((f,ts),lpp_inline_return_calls (snd (P!c)),lpp_inline_return_guards (snd (P!c)))\<in>set SP"
      using selected[OF f] by auto
    have "lpc_model_program [(fst (P!c),snd (P!c))] (lpp_inline_return_model SP E)"
      by (rule lpp_inline_return_clause[OF head ordinary body clause])
    then show ?thesis by simp
  qed
  show "\<exists>g ts. fst (P!c)=Fun g ts \<and> (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow>
    list_all (lpc_return_control_goal F) (snd (P!c)) \<and> lpc_model_program [P!c] (lpp_inline_return_model SP E))"
    using head selected model by blast
qed


lemma lpp_success_guard_evaluation_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and holds: "lpp_success_guard_holds E eta g"
  shows "lpp_success_guard_holds E (\<lambda>x. lp_isubst (eta x) sigma) g"
  using holds by (cases g) (auto simp: lp_ieval_subst[symmetric]
    intro: lpp_is_integer_subst stable)

lemma lpp_guarded_success_evaluation_subst:
  fixes a :: "'w lpp_success_iatom" and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and success: "lpp_guarded_success P E a"
  shows "lpp_guarded_success P E (lpp_success_iatom_subst a sigma)"
  using success
proof (induct rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  have guards: "list_all (lpp_success_guard_holds E (\<lambda>x. lp_isubst (eta x) sigma)) gs"
    using clause.hyps by (auto simp: list_all_iff intro: lpp_success_guard_evaluation_subst[where E=E, OF stable])
  have body: "list_all (lpp_guarded_success P E)
    (map (\<lambda>b. lpp_success_atom_eval b (\<lambda>x. lp_isubst (eta x) sigma)) bs)"
    using clause.hyps by (auto simp: list_all_iff lpp_success_atom_eval_subst[symmetric])
  show ?case unfolding lpp_success_atom_eval_subst
    by (rule lpp_guarded_success.clause[OF clause.hyps(1) guards body])
qed

lemma lpp_inline_return_model_subst:
  fixes t :: "(string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and known: "lpp_inline_return_model SP E t"
  shows "lpp_inline_return_model SP E (lp_isubst t sigma)"
proof (cases t)
  case (LPIVar v)
  then show ?thesis using known by simp
next
  case (LPIFun f ts)
  have mapped: "lpp_guarded_success SP E (g,us) \<Longrightarrow>
    lpp_guarded_success SP E (g,map (\<lambda>t. lp_isubst t sigma) us)" for g us
    using lpp_guarded_success_evaluation_subst[where E=E and a="(g,us)" and sigma=sigma, OF stable]
    by (simp add: lpp_success_iatom_subst_def)
  show ?thesis using known LPIFun
    by (cases f) (auto intro: stable lpp_is_integer_subst dest: mapped)
qed


lemma lpp_checked_operation_context_evaluation:
  fixes SP :: "'v lpp_success_clause list" and ps :: "'v lpp_success_atom list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_operation_context T ps gs fs K"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and prefix: "list_all (lpp_guarded_success SP E)
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_integer_known K eta"
proof -
  have check: "lpp_check_path_types T ps gs fs"
    using checked by (simp add: lpp_check_operation_context_def)
  have known: "lpp_integer_known (map lpp_transfer_variable fs) eta"
    by (rule lpp_check_path_types_sound[where eta=eta and E=E, OF program check guards prefix evaluation])
  show ?thesis using known checked
    by (auto simp: lpp_check_operation_context_def lpp_integer_known_def list_all_iff)
qed

theorem lpp_inline_integer_actual_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and no_probe: "\<And>f ts a keep. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinProbe a keep)"
    and no_call: "\<And>f ts a. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinCall a)"
    and no_branch: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinBranch cs ys ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and evaluation: "lpp_eval_integer_contract TYPE(string) E"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_operation_context T [(f,ts)] guards facts K"
    and guards: "list_all (lpp_success_guard_holds E eta) guards"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_integer_known K rho"
proof -
  let ?M = "lpp_inline_return_model SP E"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_inline_return_program_sound[OF program])
  have initial: "lpc_model_goals ?M (lpp_integer_known K) ?gs eta"
  proof (unfold lpc_model_goals_def, intro conjI allI impI)
    show "list_all lpc_model_safe_goal ?gs" by simp
  next
    fix sigma assume model: "list_all (lpc_model_goal ?M)
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs)"
    have success: "list_all (lpp_guarded_success SP E)
      (map (\<lambda>b. lpp_success_atom_eval b (\<lambda>x. lp_isubst (eta x) sigma)) [(f,ts)])"
      using model by (simp add: ordinary lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
    have observed: "list_all (lpp_success_guard_holds E
      (\<lambda>x. lp_isubst (eta x) sigma)) guards"
      using guards by (auto simp: list_all_iff intro: lpp_success_guard_evaluation_subst[where E=E, OF stable])
    show "lpp_integer_known K (\<lambda>x. lp_isubst (eta x) sigma)"
      by (rule lpp_checked_operation_context_evaluation[OF transfer typing observed success evaluation])
  qed
  have known: "list_all (lpc_scoped_model_frame F ?M (lpp_integer_known K)) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_scoped_model_actual_return_without_probe[OF modeled builtin no_probe no_call no_branch no_choice
    lpp_inline_return_model_subst[where E=E, OF stable] known actual])
qed

ML \<open>
val checked = [@{thm lpp_inline_integer_actual_return}, @{thm lpp_inline_return_program_sound},
  @{thm lpp_finite_evaluation_integer_contract}, @{thm lpp_finite_evaluation_subst}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted inline source return dependency" else ();
\<close>
end
