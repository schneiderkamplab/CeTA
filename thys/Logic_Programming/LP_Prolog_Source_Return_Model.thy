theory LP_Prolog_Source_Return_Model
 imports LP_Prolog_Scoped_Return_Models LP_Prolog_Guarded_Returns
begin

fun lpp_source_return_model :: "string lpp_success_clause list \<Rightarrow> (string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool" where
  "lpp_source_return_model SP (LPIFun (LPCUser f) ts) =
    lpp_guarded_success SP lpp_integer_result (f,ts)"
| "lpp_source_return_model SP _ = False"

fun lpp_source_return_calls :: "(string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> string lpp_success_atom list" where
  "lpp_source_return_calls [] = []"
| "lpp_source_return_calls (LPCAtom (Fun (LPCUser f) ts)#gs) =
    (f,ts)#lpp_source_return_calls gs"
| "lpp_source_return_calls (g#gs) = lpp_source_return_calls gs"

lemma lpp_source_return_safe:
  "list_all (lpc_return_control_goal F) gs \<Longrightarrow> list_all lpc_model_safe_goal gs"
  by (auto simp: list_all_iff lpc_return_control_goal_iff lpc_control_goal_iff)

lemma lpp_source_return_body:
  assumes control: "list_all (lpc_return_control_goal F) gs"
    and model: "list_all (lpc_model_goal (lpp_source_return_model SP))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  shows "list_all (lpp_guarded_success SP lpp_integer_result)
    (map (\<lambda>b. lpp_success_atom_eval b eta) (lpp_source_return_calls gs))"
  using control model
  by (induct gs) (auto simp: lpc_return_control_goal_iff lpc_control_goal_iff lpp_success_atom_eval_def)

definition lpp_source_return_program_check :: "(string,string) lp_cut_program \<Rightarrow> string set \<Rightarrow> string lpp_success_clause list \<Rightarrow> bool" where
  "lpp_source_return_program_check P F SP = (\<forall>c<length P. \<exists>f ts.
    fst (P!c)=Fun (LPCUser f) ts \<and> (f\<in>F \<longrightarrow>
      list_all (lpc_return_control_goal F) (snd (P!c)) \<and>
      ((f,ts),lpp_source_return_calls (snd (P!c)),[])\<in>set SP))"

lemma lpp_source_return_program_check_code[code]:
  "lpp_source_return_program_check P F SP = list_all (\<lambda>c.
    case fst c of Fun (LPCUser f) ts \<Rightarrow>
      (f\<in>F \<longrightarrow> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_source_return_calls (snd c),[])\<in>set SP)
    | _ \<Rightarrow> False) P"
proof -
  have local: "(\<exists>f ts. fst c=Fun (LPCUser f) ts \<and>
      (f\<in>F \<longrightarrow> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_source_return_calls (snd c),[])\<in>set SP)) =
    (case fst c of Fun (LPCUser f) ts \<Rightarrow>
      (f\<in>F \<longrightarrow> list_all (lpc_return_control_goal F) (snd c) \<and>
        ((f,ts),lpp_source_return_calls (snd c),[])\<in>set SP) | _ \<Rightarrow> False)" for c
  proof (cases "fst c")
    case (Var x) then show ?thesis by simp
  next
    case (Fun g ts) then show ?thesis by (cases g) auto
  qed
  show ?thesis by (simp only: lpp_source_return_program_check_def local; simp only: list_all_length)
qed

lemma lpp_source_return_clause:
  assumes head: "h=Fun (LPCUser f) ts"
    and control: "list_all (lpc_return_control_goal F) gs"
    and clause: "((f,ts),lpp_source_return_calls gs,[])\<in>set SP"
  shows "lpc_model_program [(h,gs)] (lpp_source_return_model SP)"
proof -
  have safe: "list_all lpc_model_safe_goal gs" by (rule lpp_source_return_safe[OF control])
  have closed: "lpp_source_return_model SP (lp_ieval h eta)"
    if model: "list_all (lpc_model_goal (lpp_source_return_model SP))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)" for eta m
  proof -
    have body: "list_all (lpp_guarded_success SP lpp_integer_result)
      (map (\<lambda>b. lpp_success_atom_eval b eta) (lpp_source_return_calls gs))"
      by (rule lpp_source_return_body[OF control model])
    have success: "lpp_guarded_success SP lpp_integer_result (lpp_success_atom_eval (f,ts) eta)"
      by (rule lpp_guarded_success.clause[OF clause _ body]) simp
    show ?thesis using success by (simp add: head lpp_success_atom_eval_def)
  qed
  show ?thesis using safe closed by (auto simp: lpc_model_program_def)
qed

theorem lpp_source_return_program_sound:
  assumes checked: "lpp_source_return_program_check P F SP"
  shows "lpc_scoped_model_program P F (lpp_source_return_model SP)"
proof (unfold lpc_scoped_model_program_def, intro allI impI)
  fix c assume index: "c<length P"
  obtain f ts where head: "fst (P!c)=Fun (LPCUser f) ts"
    and selected: "f\<in>F \<Longrightarrow> list_all (lpc_return_control_goal F) (snd (P!c)) \<and>
      ((f,ts),lpp_source_return_calls (snd (P!c)),[])\<in>set SP"
    using checked index by (auto simp: lpp_source_return_program_check_def)
  have model: "lpc_model_program [P!c] (lpp_source_return_model SP)" if f: "f\<in>F"
  proof -
    have body: "list_all (lpc_return_control_goal F) (snd (P!c))"
      and clause: "((f,ts),lpp_source_return_calls (snd (P!c)),[])\<in>set SP"
      using selected[OF f] by auto
    have "lpc_model_program [(fst (P!c),snd (P!c))] (lpp_source_return_model SP)"
      by (rule lpp_source_return_clause[OF head body clause])
    then show ?thesis by simp
  qed
  show "\<exists>g ts. fst (P!c)=Fun g ts \<and> (\<forall>f. g=LPCUser f \<longrightarrow> f\<in>F \<longrightarrow>
    list_all (lpc_return_control_goal F) (snd (P!c)) \<and> lpc_model_program [P!c] (lpp_source_return_model SP))"
    using head selected model by blast
qed

lemma lpp_source_return_model_subst:
  assumes known: "lpp_source_return_model SP t"
  shows "lpp_source_return_model SP (lp_isubst t sigma)"
proof (cases t)
  case (LPIVar v)
  then show ?thesis using known by simp
next
  case (LPIFun f ts)
  then show ?thesis using known
    by (cases f) (auto simp: lpp_success_iatom_subst_def dest: lpp_guarded_success_integer_subst)
qed

end
