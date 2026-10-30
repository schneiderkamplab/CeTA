theory LP_Prolog_Arithmetic_Return_Check
  imports LP_Prolog_Integer_Builtins LP_Cut_Return_Table_Equality
begin

text \<open>Symbolic arithmetic reuses the existing return-aware equality
checker. A fresh observation variable holds the evaluated integer. Its value
must not change the source stack, saved returns, parent interface or prior
guards. Integer-domain premises remain explicit obligations of the caller.\<close>

fun lpp_fresh_entry where
  "lpp_fresh_entry x (LPCGoals gs) = (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). x\<notin>vars_term t)"
| "lpp_fresh_entry x (LPCClause gs c m) = (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). x\<notin>vars_term t)"
| "lpp_fresh_entry x (LPCBarrier m) = True"
definition lpp_fresh_return where
  "lpp_fresh_return x ss = (\<forall>(e,ts)\<in>set ss. lpp_fresh_entry x e \<and> (\<forall>t\<in>set ts. x\<notin>vars_term t))"
fun lpp_fresh_guard where
  "lpp_fresh_guard x (LPCHeadGuard a h b) = (x\<notin>vars_term a)"
| "lpp_fresh_guard x (LPCEqGuard a b truth) = (x\<notin>vars_term a \<and> x\<notin>vars_term b)"

lemma lpp_fresh_term_eval:
  "x\<notin>vars_term t \<Longrightarrow> lp_ieval t (eta(x:=v))=lp_ieval t eta"
  by (rule lp_ieval_cong) auto

lemma lpp_fresh_goal_eval:
  "(\<forall>t\<in>set (lp_cut_terms g). x\<notin>vars_term t) \<Longrightarrow>
    lp_cut_map (\<lambda>t. lp_ieval t (eta(x:=v))) g=lp_cut_map (\<lambda>t. lp_ieval t eta) g"
  by (cases g) (auto simp: lpp_fresh_term_eval)

lemma lpp_fresh_entry_eval:
  "lpp_fresh_entry x e \<Longrightarrow>
    lp_cut_entry_map (\<lambda>t. lp_ieval t (eta(x:=v))) e=lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e"
  by (cases e) (auto intro!: map_cong lpp_fresh_goal_eval)

lemma lpp_fresh_return_eval:
  assumes fresh: "lpp_fresh_return x ss"
  shows "lpc_return_eval (eta(x:=v)) ss=lpc_return_eval eta ss"
proof (unfold lpc_return_eval_def, rule map_cong[OF refl])
  fix frame assume member: "frame\<in>set ss"
  obtain e ts where frame: "frame=(e,ts)" by (cases frame) auto
  have fe: "lpp_fresh_entry x e" and ft: "\<forall>t\<in>set ts. x\<notin>vars_term t"
    using fresh member frame by (auto simp: lpp_fresh_return_def)
  have env: "lpc_return_env ts (eta(x:=v))=lpc_return_env ts eta"
    by (rule lpc_return_env_cong, rule map_cong[OF refl], rule lpp_fresh_term_eval)
      (use ft in auto)
  show "(case frame of (e,ts) \<Rightarrow>
      (lp_cut_entry_map (\<lambda>t. lp_ieval t (eta(x:=v))) e,lpc_return_env ts (eta(x:=v)))) =
    (case frame of (e,ts) \<Rightarrow> (lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,lpc_return_env ts eta))"
    using lpp_fresh_entry_eval[OF fe, of eta v] env by (simp add: frame)
qed

lemma lpp_fresh_guard_eval:
  "lpp_fresh_guard x g \<Longrightarrow> lp_cut_guard_holds g (eta(x:=v))=lp_cut_guard_holds g eta"
  by (cases g) (auto simp: lpp_fresh_term_eval)

lemma lpp_fresh_integer_knowledge:
  assumes known: "lp_cut_knowledge (set G) guards eta"
    and fresh: "list_all (lpp_fresh_guard x) guards"
  shows "lp_cut_knowledge (set (x#G)) guards (eta(x:=lpp_integer_value n))"
  using known fresh lpp_fresh_guard_eval[of x _ eta "lpp_integer_value n"]
  by (auto simp: lp_cut_knowledge_def list_all_iff lpp_integer_value_def intro: lp_seg_ground.intros)

definition lpp_check_integer_is_node where
  "lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l next mode outputs yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     lpcn_state nd=map fst ss \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check K evidence \<and>
     lpp_fresh_return result_var ss \<and> result_var\<notin>set (lpcn_vars nd) \<and>
     list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpc_check_return_equality_node fuel P Q nds states
       (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>) a (Var result_var) gs active saved k l next mode outputs yes no)"

theorem lpp_integer_is_node_sound:
  assumes checked: "lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e gs active saved result_var k l next mode outputs yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and integers: "lpp_integer_known K eta"
    and exact: "\<And>outcome. U ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
      lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome"
    and step: "lpp_answer_transition P lpp_builtin_signature U (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    and result_var: "lpp_fresh_return result_var ss"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and equality: "lpc_check_return_equality_node fuel P Q nds states
      (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>) a (Var result_var) gs active saved k l next mode outputs yes no"
    using checked by (auto simp: lpp_check_integer_is_node_def)
  obtain n where evaluated: "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed integers] expr by blast
  let ?nu = "eta(result_var:=lpp_integer_value n)"
  have source: "lpc_answer_transition P
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_checked_is_uses_shared_equality[where U=U, OF evaluated exact])
      (use step in \<open>simp add: shape lpc_return_eval_def\<close>)
  have fa: "result_var\<notin>vars_term a" and rest:
    "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved) =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "lpp_integer_value n"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (lpcn_ground (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>)))
      (lpcn_guards (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>)) ?nu"
    using lpp_fresh_integer_knowledge[OF known guards, of n] by simp
  have actual: "lpc_answer_transition P (lpc_return_eval ?nu
    ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)) event tt"
    using source by (simp only: represented)
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  show ?thesis using lpc_return_equality_node_sound[OF equality extended actual]
    by (simp add: parent)
qed

end
