theory LP_Prolog_Var_Test
  imports LP_Prolog_Answers LP_Prolog_Builtin_Signature LP_Cut_Return_Table
begin

text \<open>Variable tests inspect the root constructor only, including on
rational values. They neither bind variables nor create choice points. Finite
runtime inspection is represented by a total case distinction. Unknown input
shape requires both outcomes; groundness justifies nonvar, not an integer type.\<close>

fun lpp_is_var where
  "lpp_is_var (LPIVar x) = True"
| "lpp_is_var (LPIFun f ts) = False"

fun lpp_is_compound where
  "lpp_is_compound (LPIVar x) = False"
| "lpp_is_compound (LPIFun f ts) = (ts\<noteq>[])"

definition lpp_var_name where
  "lpp_var_name f = (f=''1:var'' \<or> f=''1:nonvar'' \<or> f=''1:compound'' \<or> f=''1:atomic'')"

definition lpp_var_holds where
  "lpp_var_holds f t = (if f=''1:var'' then lpp_is_var t else if f=''1:nonvar'' then \<not>lpp_is_var t else if f=''1:compound'' then lpp_is_compound t else \<not>lpp_is_var t \<and> \<not>lpp_is_compound t)"

definition lpp_var_builtin where
  "lpp_var_builtin f ts result = (lpp_var_name f \<and> (\<exists>t. ts=[t] \<and>
    result = (if lpp_var_holds f t then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)))"

lemma lpp_var_selected:
  "lpp_var_name f \<Longrightarrow> (f,1)\<in>lpp_builtin_signature"
  by (auto simp: lpp_var_name_def lpp_builtin_signature_def)

lemma lpp_goal_map_identity[simp]:
  "lp_cut_map (\<lambda>x. x) g = g"
  by (cases g) simp_all

lemma lpp_goal_map_identity_fun[simp]:
  "lp_cut_map (\<lambda>x. x) = id"
  by (rule ext) simp

lemma lpp_var_step_exact:
  assumes name: "lpp_var_name f"
  shows "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin
      ((LPCGoals (LPCAtom (LPIFun (LPCUser f) [a])#gs),eta)#es) event tt
    \<longleftrightarrow> event=None \<and>
      tt=(if lpp_var_holds f a then (LPCGoals gs,eta)#es else es)"
proof (cases "lpp_var_holds f a")
  case True
  have outcome: "\<And>r. lpp_var_builtin f [a] r \<longleftrightarrow> r=LPPBuiltinSuccess LPIVar"
    using name True by (simp add: lpp_var_builtin_def)
  show ?thesis using lpp_builtin_success_only[where ts="[a]" and f=f and sigma=LPIVar and U=lpp_var_builtin and B=lpp_builtin_signature and P=P and gs=gs and eta=eta and es=es and event=event and tt=tt] lpp_var_selected[OF name] outcome True
    by (simp; blast)
next
  case False
  have outcome: "\<And>r. lpp_var_builtin f [a] r \<longleftrightarrow> r=LPPBuiltinFailure"
    using name False by (simp add: lpp_var_builtin_def)
  show ?thesis using lpp_builtin_failure_only[where ts="[a]" and f=f and U=lpp_var_builtin and B=lpp_builtin_signature and P=P and gs=gs and eta=eta and es=es and event=event and tt=tt] lpp_var_selected[OF name] outcome False
    by (simp; blast)
qed

fun lpp_var_outcomes where
  "lpp_var_outcomes f G (Var x) =
    (if (f=''1:var'' \<or> f=''1:nonvar'') \<and> x\<in>set G then [f=''1:nonvar''] else [False,True])"
| "lpp_var_outcomes f G (Fun g ts) = [if f=''1:var'' then False else if f=''1:nonvar'' then True else if f=''1:compound'' then ts\<noteq>[] else ts=[]]"

lemma lpp_var_outcomes_cover:
  assumes name: "lpp_var_name f" and known: "lp_cut_knowledge (set G) guards eta"
  shows "lpp_var_holds f (lp_ieval a eta)\<in>set (lpp_var_outcomes f G a)"
proof (cases a)
  case (Fun g ts)
  then show ?thesis using name by (auto simp: lpp_var_name_def lpp_var_holds_def split: if_splits)
next
  case (Var x)
  show ?thesis
  proof (cases "x\<in>set G")
    case False
    then show ?thesis using Var by auto
  next
    case True
    have ground: "lp_seg_ground (eta x)" using known True by (simp add: lp_cut_knowledge_def)
    have "\<not>lpp_is_var (eta x)" using ground by (cases rule: lp_seg_ground.cases) simp
    then show ?thesis using name Var True by (auto simp: lpp_var_name_def lpp_var_holds_def split: if_splits)
  qed
qed

definition lpp_check_var_node where
  "lpp_check_var_node fuel Q nds states nd ss f a gs active saved yes no =
    (lpp_var_name f \<and> ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved \<and>
     list_all (\<lambda>b. lpc_check_return_table_link fuel Q nds states nd
       (if b then (LPCGoals gs,active)#saved else saved)
       (lpcn_ground nd) (lpcn_guards nd) [] (if b then yes else no))
       (lpp_var_outcomes f (lpcn_ground nd) a))"

theorem lpp_var_node_sound:
  assumes checked: "lpp_check_var_node fuel Q nds states nd ss f a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin
      (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and> event=None"
proof -
  let ?b = "lpp_var_holds f (lp_ieval a eta)"
  let ?next = "if ?b then (LPCGoals gs,active)#saved else saved"
  have name: "lpp_var_name f" and shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
    using checked by (auto simp: lpp_check_var_node_def)
  have coverage: "?b\<in>set (lpp_var_outcomes f (lpcn_ground nd) a)"
    by (rule lpp_var_outcomes_cover[OF name known])
  have link: "lpc_check_return_table_link fuel Q nds states nd ?next
    (lpcn_ground nd) (lpcn_guards nd) [] (if ?b then yes else no)"
    using checked coverage by (auto simp: lpp_check_var_node_def list_all_iff)
  have actual: "event=None \<and> tt=lpc_return_eval eta ?next"
    using step
    by (auto simp: shape lpc_return_eval_def lpp_var_step_exact[OF name] split: if_splits)
  show ?thesis using lpc_return_table_link_sound[OF link _ refl known] actual
    by (auto simp: lp_equations_def)
qed

text \<open>Non-builtin frames use the unchanged cut checker. This executable
shape test never treats a variable predicate as a known ordinary call.\<close>

fun lpp_no_builtin_frame where
  "lpp_no_builtin_frame [] = True"
| "lpp_no_builtin_frame ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved) =
    ((f,length ts)\<notin>lpp_builtin_signature)"
| "lpp_no_builtin_frame ((LPCGoals (LPCAtom a#gs),active)#saved) = False"
| "lpp_no_builtin_frame ss = True"


lemma lpp_no_builtin_frame_sound:
  "lpp_no_builtin_frame ss \<Longrightarrow>
   \<not>lpp_builtin_active lpp_builtin_signature (map fst (lpc_return_eval eta ss))"
  by (induct ss rule: lpp_no_builtin_frame.induct)
    (auto simp: lpc_return_eval_def lpp_builtin_active_def)

lemma lpp_var_builtin_selected:
  "lpp_var_builtin f ts result \<Longrightarrow> (f,length ts)\<in>lpp_builtin_signature"
  using lpp_var_selected by (auto simp: lpp_var_builtin_def)

lemma lpp_nonbuiltin_answer_base:
  assumes clear: "lpp_no_builtin_frame ss"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin
      (lpc_return_eval eta ss) event tt"
  shows "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  using step lpp_no_builtin_frame_sound[OF clear, of eta]
  by (cases rule: lpp_answer_transition.cases)
    (auto simp: lpp_builtin_active_def dest: lpp_var_builtin_selected)

end
