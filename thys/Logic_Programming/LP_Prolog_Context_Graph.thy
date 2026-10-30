theory LP_Prolog_Context_Graph
 imports LP_Prolog_Context_Source_Actions
begin
definition lpp_check_context_graph where
  "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     length nds=length contexts \<and> length nds=length typings \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_source_types (actions!i)) \<and>
       lpp_check_context_source_action fuel P Q nds states contexts (nds!i) (states!i) (contexts!i) returned arity (actions!i)) [0..<length nds])"

lemma lpp_context_graph_valid:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
  shows "lp_answer_graph_valid (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
  proof (rule lpp_return_graph_scope_valid[OF program])
    fix ss t event tt
    assume rep: "lpp_context_return_rep SP nds states contexts ss t"
      and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin ss event tt"
    obtain j nu where j: "j<length nds" and ss: "ss=lpc_return_eval nu (states!j)"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
      and facts: "lpp_source_context_holds SP (contexts!j) nu"
      and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
      using rep unfolding lpp_context_return_rep_def by blast
    have action: "lpp_check_context_source_action fuel P Q nds states contexts (nds!j) (states!j) (contexts!j) returned arity (actions!j)"
      using checked j by (auto simp: lpp_check_context_graph_def list_all_iff)
    have typing: "lpp_check_context_typing T (contexts!j) (typings!j) (lpp_context_source_types (actions!j))"
      using checked j by (auto simp: lpp_check_context_graph_def list_all_iff)
    have integers: "lpp_integer_known (lpp_context_source_types (actions!j)) nu"
      by (rule lpp_context_typing_sound[OF transfer typing facts])
    show "(\<exists>u swaps. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and> lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpp_context_source_action_sound[OF action knowledge facts integers, of event tt] step by (simp add: ss t)
  qed

theorem lpp_check_context_graph_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and program: "lp_cut_source_program P"
    and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpp_return_contract P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  have valid: "lp_answer_graph_valid (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
    by (rule lpp_context_graph_valid[OF checked transfer program])
  have bound: "i<length states" "i<length contexts" using checked root by (simp_all add: lpp_check_context_graph_def)
  have represented: "\<exists>swaps. lpp_context_return_rep SP nds states contexts
    (lpc_return_scope_word swaps (lpc_return_eval eta (states!i)))
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
      unfold lpp_context_return_rep_def, rule exI[of _ i], rule exI[of _ eta])
      (use root bound known observed in auto)
  show ?thesis by (rule lpp_return_graph_contract[OF valid residual represented])
qed

lemma lpp_context_graph_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and represented: "lpp_context_return_rep SP nds states contexts ss t"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst ss)"
proof -
  obtain j nu where j: "j<length nds" and ss: "ss=lpc_return_eval nu (states!j)"
    and facts: "lpp_source_context_holds SP (contexts!j) nu"
    using represented unfolding lpp_context_return_rep_def by blast
  have action: "lpp_check_context_source_action fuel P Q nds states contexts (nds!j) (states!j) (contexts!j) returned arity (actions!j)"
    and typing: "lpp_check_context_typing T (contexts!j) (typings!j) (lpp_context_source_types (actions!j))"
    using checked j by (auto simp: lpp_check_context_graph_def list_all_iff)
  have integers: "lpp_integer_known (lpp_context_source_types (actions!j)) nu"
    by (rule lpp_context_typing_sound[OF transfer typing facts])
  show ?thesis using lpp_context_source_action_domain[OF action integers] by (simp add: ss)
qed

lemma lpp_builtin_domain_bad_scope:
  "lpp_builtin_domain_bad B D (map (lp_cut_scope_entry r) ss)=lpp_builtin_domain_bad B D ss"
  by (cases "(B,D,ss)" rule: lpp_builtin_domain_bad.cases) auto

lemma lpp_builtin_domain_bad_scopes:
  "lpp_builtin_domain_bad B D (map fst (lpc_return_scope_word swaps ss)) = lpp_builtin_domain_bad B D (map fst ss)"
proof (induct swaps arbitrary: ss)
  case Nil show ?case by simp
next
  case (Cons swap swaps)
  obtain a b where pair: "swap=(a,b)" by (cases swap) auto
  have unchanged: "lpp_builtin_domain_bad B D (map (lp_cut_scope_entry (lp_cut_scope_swap a b)) (map fst ss)) =
    lpp_builtin_domain_bad B D (map fst ss)"
    by (rule lpp_builtin_domain_bad_scope)
  show ?case using unchanged by (simp add: pair Cons.hyps map_map o_def map_prod_def split_def)
qed

lemma lpp_context_domain_graph_valid:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
  shows "lp_answer_graph_valid
    (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain) (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
proof -
  have valid: "lp_answer_graph_valid (lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin) (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
    by (rule lpp_context_graph_valid[OF checked transfer program])
  have safe: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst ss)"
    if "\<exists>swaps. lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps ss) t" for ss t
    using lpp_context_graph_domain[OF checked transfer] that lpp_builtin_domain_bad_scopes by blast
  show ?thesis using valid safe by (auto simp: lp_answer_graph_valid_def lpp_domain_answers_def)
qed

definition lpp_check_context_root where
  "lpp_check_context_root fuel P Q nds states contexts T typings returned arity actions i =
    (lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions \<and>
     i<length nds \<and> contexts!i=([],[],[]))"

theorem lpp_context_root_domain_SN:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_root fuel P Q nds states contexts T typings returned arity actions i"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!i))}"
proof -
  have graph: "lpp_check_context_graph fuel P Q nds states contexts T typings returned arity actions"
    and root: "i<length nds" and empty: "contexts!i=([],[],[])"
    using checked by (auto simp: lpp_check_context_root_def)
  have bound: "i<length states" "i<length contexts"
    using graph root by (simp_all add: lpp_check_context_graph_def)
  have observed: "lpp_source_context_holds SP (contexts!i) eta"
    by (simp add: empty lpp_path_context_holds_def)
  have represented: "\<exists>swaps. lpp_context_return_rep SP nds states contexts
    (lpc_return_scope_word swaps (lpc_return_eval eta (states!i)))
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
      unfold lpp_context_return_rep_def, rule exI[of _ i], rule exI[of _ eta])
      (use root bound known observed in auto)
  show ?thesis by (rule lpp_domain_instrumentation_SN,
    rule lp_answer_graph_SN[OF lpp_context_domain_graph_valid[OF graph transfer program] residual represented])
qed

ML \<open>
val checked = [@{thm lpp_context_root_domain_SN}, @{thm lpp_check_context_graph_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source graph dependency" else ();
\<close>
end
