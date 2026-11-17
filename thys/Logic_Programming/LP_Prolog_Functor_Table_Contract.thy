theory LP_Prolog_Functor_Table_Contract
 imports LP_Prolog_Functor_Control_Contract
begin

text \<open>A node obligation includes actual return behavior and the invariant. A
  missing local action denotes an explicit module obligation, never a proof.\<close>

definition lpp_functor_node_contract where
 "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i =
  (\<forall>eta. lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   J (lpc_return_eval eta (states!i)) \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v \<longrightarrow> J vs \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
    (\<lambda>rho. [(returned,map rho [0..<arity])]))"

lemma lpp_functor_cut_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFCut action yes_facts no_facts)"
 and stable: "\<And>eta ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow> J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_functor_control_cut_contract[where J=J, OF compatible transfer checked])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal using stable by blast
 subgoal by blast
 done

lemma lpp_functor_test_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFTest yes no yes_facts no_facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)"
 and stable: "\<And>eta ev ys. lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow> J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_functor_control_test_contract[where J=J, OF compatible transfer checked shape])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal using stable by blast
 subgoal by blast
 done

lemma lpp_functor_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFIs result_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)"
 and normalized: "\<And>eta f. J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_functor_control_is_contract[where J=J, OF compatible transfer checked shape])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal using normalized by blast
 subgoal by blast
 done

lemma lpp_functor_univ_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts (nds!i) (Fs!i) (states!i)
   (contexts!i) (functor_contexts!i) returned arity (LPPFUniv value_var name_var args_var middle facts)"
 and shape: "(states!i)=((LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [a,b])#gs),active)#saved)"
 and normalized: "\<And>eta f ts. lp_ieval a eta=LPIFun f ts \<Longrightarrow> J (lpc_return_eval eta (states!i)) \<Longrightarrow>
   J ((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval b eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)"

 shows "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 unfolding lpp_functor_node_contract_def
 apply (intro allI impI)
 apply (rule lpp_functor_control_univ_contract[where J=J, OF compatible transfer checked shape])
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal by assumption
 subgoal using normalized by blast
 subgoal by blast
 done

theorem lpp_functor_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
 and program: "lp_cut_source_program P"
 and scopes: "\<And>swaps ss. J ss \<Longrightarrow> J (lpc_return_scope_word swaps ss)"
 and local: "\<And>j action. j<length nds \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity j"
 and root: "i<length nds"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "J (lpc_return_eval eta (states!i))"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
   (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?ret = "\<lambda>rho. [(returned,map rho [0..<arity])]"
 let ?rep = "\<lambda>ss t out. out=?ret \<and> J ss \<and> SN_on (lp_ild Q) {t} \<and>
   lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts ss t"
 have bounds: "i<length states" "i<length contexts" "i<length Fs" "i<length functor_contexts"
  using checked root by (auto simp: lpp_check_functor_control_def)
 have initial: "?rep (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] ?ret"
  using invariant residual lpp_stable_functor_module_intro[OF root bounds known free observed functors] by blast
 show ?thesis
 proof (rule lp_answer_contract_modular[where rep="?rep", OF residual initial])
  fix ss t and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
    (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "?rep ss t out"
   and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow> ?rep vs v ret \<Longrightarrow>
     lp_answer_contract ?T vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
   and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
   and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
   and fresh: "lpc_free_knowledge (set (Fs!j)) nu"
   and observations: "lpp_stable_context_holds operation SP (contexts!j) nu"
   and facts: "list_all (lpp_functor_fact_holds names nu) (functor_contexts!j)"
   and subject: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
   using represented by (auto simp: lpp_stable_functor_module_rep_def lpp_stable_functor_rep_def)
  have inv: "J (lpc_return_eval nu (states!j))"
   using scopes[of ss swaps] represented shape by auto
  have node: "lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity j"
   by (cases "actions!j") (use local boundary bound in auto)
  have sn: "SN_on (lp_ild Q) {t}" using represented by simp
  have descendants: "lp_answer_contract ?T vs (lp_ild Q) v ?ret"
   if "(t,v)\<in>(lp_ild Q)\<^sup>+"
    "lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts vs v" "J vs" for vs v
  proof -
   have child_sn: "SN_on (lp_ild Q) {v}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
      (use trancl_into_rtrancl[OF that(1)] in auto)
   show ?thesis by (rule lower[OF that(1)]) (use that child_sn in auto)
  qed
  have canonical: "lp_answer_contract ?T (lpc_return_eval nu (states!j)) (lp_ild Q) t ?ret"
   using node knowledge fresh observations facts inv sn descendants unfolding lpp_functor_node_contract_def subject by blast
  have restored: "lp_answer_contract ?T (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t ?ret"
   by (rule lpp_domain_contract_scopes[OF program canonical])
  show "lp_answer_contract ?T ss (lp_ild Q) t out"
   using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
 qed
qed

ML \<open>
val checked = @{thms lpp_functor_table_contract lpp_functor_cut_node_contract lpp_functor_test_node_contract lpp_functor_is_node_contract lpp_functor_univ_node_contract};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted functor table contract dependency" else ();
\<close>
end
