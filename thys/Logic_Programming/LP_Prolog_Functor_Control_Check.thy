theory LP_Prolog_Functor_Control_Check
 imports LP_Prolog_Stable_Functor_Actions LP_Prolog_Functor_Observed_Is LP_Prolog_Univ_Stable_Context
begin

text \<open>This is a versioned local proof table for the established graph.
It uses the shared states and action checks. None marks an explicit module
boundary whose contract must be supplied by composition; it is not a solved
node. The table check alone makes no termination claim.\<close>

datatype lpp_functor_action =
   LPPFCut "string lpc_return_action" "string lpp_transfer_fact list" "string lpp_transfer_fact list"
 | LPPFTest "string lpc_link" "string lpc_link" "string lpp_transfer_fact list" "string lpp_transfer_fact list"
 | LPPFIs string "string lpc_link" "string lpp_transfer_fact list"
 | LPPFUniv string string string "string lpc_link" "string lpp_transfer_fact list"

definition lpp_check_functor_source_action where
 "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F ss source_context source_functors returned arity action =
  (case action of
   LPPFCut control yes_facts no_facts \<Rightarrow>
    lpp_check_functor_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
     nd F ss source_context source_functors returned arity control
  | _ \<Rightarrow> (case ss of
    (LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<Rightarrow>
     (case action of
       LPPFTest yes no yes_facts no_facts \<Rightarrow>
        (case ts of [a] \<Rightarrow> lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts
          nd F ss source_context source_functors f a gs active saved yes no | _ \<Rightarrow> False)
     | LPPFIs result_var middle facts \<Rightarrow>
        (case ts of [a,e] \<Rightarrow> (f=''2:is'' \<and>
          vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<and>
          lpp_check_observed_functor_link T facts fuel P Q nds states contexts Fs functor_contexts nd F ss
           source_context source_functors a e gs active saved result_var middle) | _ \<Rightarrow> False)
     | LPPFUniv value_var name_var args_var middle facts \<Rightarrow>
        (case ts of [a,b] \<Rightarrow> (f=''2:=..'' \<and>
          lpp_check_univ_evaluation_context T facts fuel Q nds states contexts functor_contexts Fs nd F ss
           source_context source_functors a b gs active saved value_var name_var args_var middle) | _ \<Rightarrow> False)
     | _ \<Rightarrow> False)
    | _ \<Rightarrow> False))"

definition lpp_check_functor_control where
 "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions =
  (length states=length nds \<and> length contexts=length nds \<and> length Fs=length nds \<and>
   length functor_contexts=length nds \<and> length actions=length nds \<and>
   list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
    (case actions!i of None \<Rightarrow> True | Some action \<Rightarrow>
      lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
       (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action)) [0..<length nds])"

lemma lpp_functor_control_complete:
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
 and bound: "i<length nds"
 shows "i<length states \<and> i<length contexts \<and> i<length Fs \<and> i<length functor_contexts \<and> i<length actions"
 and "map fst (states!i)=lpcn_state (nds!i)"
 and "actions!i=Some action \<Longrightarrow>
   lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
    (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity action"
 using checked bound by (auto simp: lpp_check_functor_control_def list_all_iff split: option.splits)

lemma lpp_functor_control_missing_actions_rejected:
 "nds\<noteq>[] \<Longrightarrow> \<not> lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity []"
 by (simp add: lpp_check_functor_control_def)

lemma lpp_functor_control_missing_facts_rejected:
 "nds\<noteq>[] \<Longrightarrow> \<not> lpp_check_functor_control T fuel P Q nds states contexts Fs [] returned arity actions"
 by (simp add: lpp_check_functor_control_def)

lemma lpp_functor_control_state_mismatch_rejected:
 "i<length nds \<Longrightarrow> map fst (states!i)\<noteq>lpcn_state (nds!i) \<Longrightarrow>
  \<not> lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
 using lpp_functor_control_complete(2) by blast

lemma lpp_functor_is_check_domain:
 assumes checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)
   source_context source_functors returned arity (LPPFIs result_var middle facts)"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 shows "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
proof -
 have covered: "vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
  using checked by (simp add: lpp_check_functor_source_action_def)
 have prior: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) SP source_context eta"
  using observed by (simp add: lpp_stable_context_holds_def)
 have context_ground: "\<forall>x\<in>lpp_source_context_ground source_context. lp_seg_ground (eta x)"
  by (rule lpp_evaluation_context_ground_sound[where E="lpp_stable_scalar_evaluation operation", OF _ prior])
    (auto dest: lpp_stable_scalar_evaluation_ground)
 have ground: "lp_seg_ground (lp_ieval e eta)"
  using known covered context_ground by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
 show ?thesis using ground by (simp add: lpp_finite_source_domain_def)
qed

lemma lpp_functor_action_wrong_univ_arity_rejected:
 "\<not> lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts nd F
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a])#gs),active)#saved)
   source_context source_functors returned arity (LPPFUniv value_var name_var args_var middle facts)"
 by (simp add: lpp_check_functor_source_action_def)

ML \<open>
val checked = @{thms lpp_functor_control_complete} @ [@{thm lpp_functor_is_check_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor control table dependency" else ();
\<close>
end
