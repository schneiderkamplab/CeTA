theory LP_Prolog_Functor_Premised_Table
 imports LP_Prolog_Functor_Table_Contract LP_Prolog_Separation_Univ_Transport
begin

text \<open>Node conditions belong to a particular valuation and incoming control path.
They are not assumed stable under arbitrary substitutions. Each local obligation
must establish the conditions of every represented child it uses.\<close>

definition lpp_premised_functor_rep where
  "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions ss t = (\<exists>i eta.
    i<length nds \<and> i<length states \<and> i<length contexts \<and> i<length Fs \<and> i<length functor_contexts \<and>
    node_conditions i eta \<and>
    ss=lpc_return_eval eta (states!i) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<and>
    lpc_free_knowledge (set (Fs!i)) eta \<and>
    lpp_stable_context_holds operation SP (contexts!i) eta \<and>
    list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<and>
    t=[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))])"

definition lpp_premised_functor_module_rep where
 "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ss t =
  (\<exists>swaps. lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_return_scope_word swaps ss) t)"

lemma lpp_premised_functor_module_intro:
 assumes bounds: "i<length nds" "i<length states" "i<length contexts" "i<length Fs" "i<length functor_contexts"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and premise: "node_conditions i eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 shows "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
   (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
 unfolding lpp_premised_functor_module_rep_def
 by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
     unfold lpp_premised_functor_rep_def, rule exI[of _ i], rule exI[of _ eta])
   (use assms in auto)

definition lpp_premised_functor_node_contract where
 "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts node_conditions J returned arity i =
  (\<forall>eta. node_conditions i eta \<longrightarrow> lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   J (lpc_return_eval eta (states!i)) \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>vs v. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],v)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions vs v \<longrightarrow> J vs \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_return_eval eta (states!i)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]
    (\<lambda>rho. [(returned,map rho [0..<arity])]))"

theorem lpp_premised_functor_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned arity actions"
 and program: "lp_cut_source_program P"
 and scopes: "\<And>swaps ss. J ss \<Longrightarrow> J (lpc_return_scope_word swaps ss)"
 and local: "\<And>j action. j<length nds \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts node_conditions J returned arity j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts node_conditions J returned arity j"
 and premise: "node_conditions i eta"
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
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions ss t"
 have bounds: "i<length states" "i<length contexts" "i<length Fs" "i<length functor_contexts"
  using checked root by (auto simp: lpp_check_functor_control_def)
 have initial: "?rep (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] ?ret"
  using invariant residual lpp_premised_functor_module_intro[where node_conditions=node_conditions, OF root bounds known free observed premise functors] by blast
 show ?thesis
 proof (rule lp_answer_contract_modular[where rep="?rep", OF residual initial])
  fix ss t and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
    (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "?rep ss t out"
   and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow> ?rep vs v ret \<Longrightarrow>
     lp_answer_contract ?T vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
   and node_premise: "node_conditions j nu"
   and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
   and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
   and fresh: "lpc_free_knowledge (set (Fs!j)) nu"
   and observations: "lpp_stable_context_holds operation SP (contexts!j) nu"
   and facts: "list_all (lpp_functor_fact_holds names nu) (functor_contexts!j)"
   and subject: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
   using represented by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
  have inv: "J (lpc_return_eval nu (states!j))"
   using scopes[of ss swaps] represented shape by auto
  have node: "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts node_conditions J returned arity j"
   by (cases "actions!j") (use local boundary bound in auto)
  have sn: "SN_on (lp_ild Q) {t}" using represented by simp
  have descendants: "lp_answer_contract ?T vs (lp_ild Q) v ?ret"
   if "(t,v)\<in>(lp_ild Q)\<^sup>+"
    "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions vs v" "J vs" for vs v
  proof -
   have child_sn: "SN_on (lp_ild Q) {v}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
      (use trancl_into_rtrancl[OF that(1)] in auto)
   show ?thesis by (rule lower[OF that(1)]) (use that child_sn in auto)
  qed
  have canonical: "lp_answer_contract ?T (lpc_return_eval nu (states!j)) (lp_ild Q) t ?ret"
   using node node_premise knowledge fresh observations facts inv sn descendants unfolding lpp_premised_functor_node_contract_def subject by blast
  have restored: "lp_answer_contract ?T (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t ?ret"
   by (rule lpp_domain_contract_scopes[OF program canonical])
  show "lp_answer_contract ?T ss (lp_ild Q) t out"
   using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
 qed
qed


text \<open>The unconditional specialization is exactly the earlier interface.
No old strategy atom needs to acquire new assumptions.\<close>

lemma lpp_premised_functor_rep_true:
 "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts (\<lambda>_ _. True) ss t =
  lpp_stable_functor_rep names operation SP nds states contexts Fs functor_contexts ss t"
 by (simp add: lpp_premised_functor_rep_def lpp_stable_functor_rep_def)

lemma lpp_premised_functor_module_true:
 "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts (\<lambda>_ _. True) ss t =
  lpp_stable_functor_module_rep names operation SP nds states contexts Fs functor_contexts ss t"
 by (simp add: lpp_premised_functor_module_rep_def lpp_stable_functor_module_rep_def lpp_premised_functor_rep_true)

lemma lpp_premised_functor_node_true:
 "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (\<lambda>_ _. True) J returned arity i =
  lpp_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts J returned arity i"
 by (simp add: lpp_premised_functor_node_contract_def lpp_functor_node_contract_def lpp_premised_functor_module_true)

lemma lpp_premised_functor_false_excluded:
 "\<not> lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (\<lambda>_ _. False) ss t"
 by (simp add: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)

text \<open>Separation contexts require explicit table coverage. An absent entry
is not an empty context. Interface transport consumes the actual checked binding;
it does not assert preservation under the runtime unifier.\<close>

definition lpp_separation_node_conditions where
 "lpp_separation_node_conditions separation_contexts i eta =
   (i<length separation_contexts \<and> list_all (lpp_separation_holds eta) (separation_contexts!i))"

lemma lpp_separation_node_missing_rejected:
 "\<not>lpp_separation_node_conditions [] i eta"
 by (simp add: lpp_separation_node_conditions_def)

lemma lpp_separation_node_transport:
 assumes bound: "i<length separation_contexts"
 and checked: "lpp_check_separation_transport before (separation_contexts!i) bindings"
 and known: "list_all (lpp_separation_holds eta) before"
 shows "lpp_separation_node_conditions separation_contexts i (\<lambda>x. lp_ieval (bindings x) eta)"
 using bound lpp_check_separation_transport_sound[OF checked known]
 by (simp add: lpp_separation_node_conditions_def)

ML \<open>
val checked = @{thms lpp_premised_functor_table_contract lpp_premised_functor_module_intro
 lpp_premised_functor_rep_true lpp_premised_functor_module_true lpp_premised_functor_node_true
 lpp_premised_functor_false_excluded lpp_separation_node_missing_rejected lpp_separation_node_transport};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted node-premised functor table" else ();
\<close>

end
