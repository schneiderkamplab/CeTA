theory LP_Prolog_Return_Check
  imports LP_Prolog_Var_Test LP_Cut_Return_Check
begin

lemma lpp_scope_goal_atom:
  "lp_cut_scope_goal r g = LPCAtom a \<longleftrightarrow> g = LPCAtom a"
  by (cases g) auto

lemma lpp_scope_entry_atom:
  "(\<exists>gs. lp_cut_scope_entry r e = LPCGoals (LPCAtom a # gs)) =
   (\<exists>gs. e = LPCGoals (LPCAtom a # gs))"
  by (cases e) (auto simp: map_eq_Cons_conv lpp_scope_goal_atom)

lemma lpp_builtin_active_scope:
  "lpp_builtin_active B (map fst (lpc_return_scope r ss)) = lpp_builtin_active B (map fst ss)"
  by (cases ss)
    (auto simp: lpp_builtin_active_def lpp_scope_entry_atom split: prod.splits)

lemma lpp_answer_transition_scope:
  assumes step: "lpp_answer_transition P B U ss event tt"
    and injective: "inj r" and program: "lp_cut_source_program P"
  shows "lpp_answer_transition P B U (lpc_return_scope r ss) event (lpc_return_scope r tt)"
  using step
proof (cases rule: lpp_answer_transition.cases)
  case base
  show ?thesis
    by (rule lpp_answer_transition.base)
      (use base lpc_answer_transition_scope[OF base(2) injective program]
        in \<open>auto simp only: lpp_builtin_active_scope\<close>)
next
  case (success f ts sigma gs eta es)
  have scoped: "lpp_answer_transition P B U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#map (lp_cut_scope_goal r) gs),eta)#lpc_return_scope r es)
    None ((LPCGoals (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (map (lp_cut_scope_goal r) gs)),
      \<lambda>x. lp_isubst (eta x) sigma)#lpc_return_scope r es)"
    by (rule lpp_answer_transition.success) (rule success(4))
  show ?thesis using scoped by (simp add: success(1-3) map_map o_def lp_cut_scope_goal_map)
next
  case failure
  then show ?thesis by (auto intro: lpp_answer_transition.failure)
next
  case error
  then show ?thesis by (auto intro: lpp_answer_transition.error)
qed

lemma lpp_answer_transition_scope_word:
  assumes "lpp_answer_transition P B U ss event tt" "lp_cut_source_program P"
  shows "lpp_answer_transition P B U (lpc_return_scope_word swaps ss) event (lpc_return_scope_word swaps tt)"
  using assms(1)
proof (induct swaps arbitrary: ss tt)
  case Nil then show ?case by simp
next
  case (Cons ab swaps)
  obtain a b where ab: "ab=(a,b)" by (cases ab) auto
  have first: "lpp_answer_transition P B U (lpc_return_scope (lp_cut_scope_swap a b) ss) event
    (lpc_return_scope (lp_cut_scope_swap a b) tt)"
    by (rule lpp_answer_transition_scope[OF Cons.prems lp_cut_scope_swap_injective assms(2)])
  show ?case using Cons.hyps[OF first] by (simp only: ab lpc_return_scope_word.simps)
qed

theorem lpp_return_graph_scope_valid:
  assumes program: "lp_cut_source_program P"
    and local: "\<And>ss t event tt. rep ss t \<Longrightarrow> lpp_answer_transition P B U ss event tt \<Longrightarrow>
      (\<exists>u swaps. (t,u)\<in>R\<^sup>+ \<and> rep (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*)"
  shows "lp_answer_graph_valid (lpp_answer_transition P B U) R
    (\<lambda>ss t. \<exists>swaps. rep (lpc_return_scope_word swaps ss) t) ret (\<lambda>_. 0)"
proof (unfold lp_answer_graph_valid_def, intro allI impI)
  fix ss t event tt
  assume represented: "\<exists>swaps. rep (lpc_return_scope_word swaps ss) t"
    and step: "lpp_answer_transition P B U ss event tt"
  obtain swaps where rep: "rep (lpc_return_scope_word swaps ss) t" using represented by blast
  have scoped: "lpp_answer_transition P B U (lpc_return_scope_word swaps ss) event (lpc_return_scope_word swaps tt)"
    by (rule lpp_answer_transition_scope_word[OF step program])
  obtain u more where edge: "(t,u)\<in>R\<^sup>+"
    and child: "rep (lpc_return_scope_word more (lpc_return_scope_word swaps tt)) u"
    and emit: "\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*"
    using local[OF rep scoped] by blast
  have child': "\<exists>rs. rep (lpc_return_scope_word rs tt) u"
    by (rule exI[of _ "swaps@more"]) (simp add: lpc_return_scope_word_append child)
  show "((\<exists>u. (t,u)\<in>R\<^sup>+ \<and> (\<exists>swaps. rep (lpc_return_scope_word swaps tt) u)) \<or>
    (\<exists>swaps. rep (lpc_return_scope_word swaps tt) t) \<and> (0::nat)<0) \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> (t,ret eta)\<in>R\<^sup>*)"
    using edge child' emit by blast
qed

datatype lpp_return_action = LPPRCut "string lpc_return_action"
  | LPPRVar string "string lpc_term" "string lpc_term lp_cut_goal list"
      "string lpc_term list" "string lpc_return_state" "string lpc_link" "string lpc_link"

fun lpp_check_return_action where
  "lpp_check_return_action fuel P Q nds states nd ss returned arity (LPPRCut action) =
    (lpp_no_builtin_frame ss \<and> lpc_check_return_action fuel P Q nds states nd ss returned arity action)"
| "lpp_check_return_action fuel P Q nds states nd ss returned arity (LPPRVar f a gs active saved yes no) =
    lpp_check_var_node fuel Q nds states nd ss f a gs active saved yes no"

theorem lpp_return_action_sound:
  assumes checked: "lpp_check_return_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case (LPPRCut a)
  have clear: "lpp_no_builtin_frame ss" and check: "lpc_check_return_action fuel P Q nds states nd ss returned arity a"
    using checked LPPRCut by auto
  show ?thesis by (rule lpc_return_action_sound[OF check known lpp_nonbuiltin_answer_base[OF clear step]])
next
  case (LPPRVar f a gs active saved yes no)
  have check: "lpp_check_var_node fuel Q nds states nd ss f a gs active saved yes no"
    using checked LPPRVar by simp
  show ?thesis using lpp_var_node_sound[OF check known step] by auto
qed

definition lpp_check_return_table where
  "lpp_check_return_table fuel P Q nds states returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpp_check_return_action fuel P Q nds states (nds!i) (states!i) returned arity (actions!i)) [0..<length nds])"

theorem lpp_check_return_table_contract:
  assumes checked: "lpp_check_return_table fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P"
    and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpp_return_contract P lpp_builtin_signature lpp_var_builtin (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  have valid: "lp_answer_graph_valid (lpp_answer_transition P lpp_builtin_signature lpp_var_builtin) (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpc_return_rep nds states (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
  proof (rule lpp_return_graph_scope_valid[OF program])
    fix ss t event tt
    assume rep: "lpc_return_rep nds states ss t"
      and step: "lpp_answer_transition P lpp_builtin_signature lpp_var_builtin ss event tt"
    obtain j nu where j: "j<length nds" and ss: "ss=lpc_return_eval nu (states!j)"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
      and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
      using rep unfolding lpc_return_rep_def by blast
    have action: "lpp_check_return_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
      using checked j by (auto simp: lpp_check_return_table_def list_all_iff)
    show "(\<exists>u swaps. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and> lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_return_action_sound[OF action knowledge, of event tt] step by (simp add: ss t)
  qed
  have bound: "i<length states" using checked root by (simp add: lpp_check_return_table_def)
  have represented: "\<exists>swaps. lpc_return_rep nds states
    (lpc_return_scope_word swaps (lpc_return_eval eta (states!i)))
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
      unfold lpc_return_rep_def, rule exI[of _ i], rule exI[of _ eta])
      (use root bound known in auto)
  show ?thesis by (rule lpp_return_graph_contract[OF valid residual represented])
qed

end
