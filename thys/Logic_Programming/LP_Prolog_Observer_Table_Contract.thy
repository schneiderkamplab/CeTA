theory LP_Prolog_Observer_Table_Contract
 imports LP_Prolog_Attached_Univ_Finite_Steps
begin

text \<open>Referenced observer proofs recurse on independently certified
residual subjects. The represented state is the actual attached caller state;
the helper projection is used only for graph identity and context evidence.
Every child reconstructs its own joint stack and establishes its invariant.\<close>

definition lpp_observer_node_contract where
 "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    node_conditions J rest returned i =
  (\<forall>eta swaps runtime.
   node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime)=lpc_return_eval eta (states!i) \<longrightarrow>
   J runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow> J child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned)"

lemma lpp_observer_silent_contract:
 assumes simulate: "\<And>event result.
   lpp_domain_answers P B U D (lpc_attach_answers rest (lpc_reinterface observe runtime)) event result \<Longrightarrow>
   event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface observe child) \<and>
     (subject,u)\<in>R\<^sup>+ \<and> represented child u \<and> J child)"
 and lower: "\<And>child u. (subject,u)\<in>R\<^sup>+ \<Longrightarrow> represented child u \<Longrightarrow> J child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface observe child)) R u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe runtime)) R subject returned"
proof (rule lp_answer_contract_intro)
 fix event result
 assume step: "lpp_domain_answers P B U D (lpc_attach_answers rest (lpc_reinterface observe runtime)) event result"
 obtain child u where silent: "event=None"
 and exact: "result=lpc_attach_answers rest (lpc_reinterface observe child)"
 and strict: "(subject,u)\<in>R\<^sup>+"
 and rep: "represented child u" and invariant: "J child"
  using simulate[OF step] by blast
 have contract: "lp_answer_contract (lpp_domain_answers P B U D) result R subject returned"
  unfolding exact by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep invariant]])
 show "(\<forall>rho. event=Some rho \<longrightarrow> (subject,returned rho)\<in>R\<^sup>*) \<and>
   lp_answer_contract (lpp_domain_answers P B U D) result R subject returned"
  using silent contract by simp
qed

theorem lpp_observer_table_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes checked: "lpp_check_functor_control T fuel P Q nds states contexts Fs functor_contexts returned_symbol arity actions"
 and local: "\<And>j action. j<length nds \<Longrightarrow> actions!j=Some action \<Longrightarrow>
   lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned j"
 and boundary: "\<And>j. j<length nds \<Longrightarrow> actions!j=None \<Longrightarrow>
   lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned j"
 and represented: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
   (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime) subject"
 and invariant: "J runtime"
 and residual: "SN_on (lp_ild Q) {subject}"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) subject returned"
proof -
 let ?T = "lpp_domain_answers P B U D"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?rep = "\<lambda>ss t out. out=returned \<and> SN_on (lp_ild Q) {t} \<and>
   (\<exists>joint. ss=lpc_attach_answers rest (lpc_reinterface ?R joint) \<and> J joint \<and>
     lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
      (lpc_reinterface ?L joint) t)"
 have initial: "?rep (lpc_attach_answers rest (lpc_reinterface ?R runtime)) subject returned"
  using represented invariant residual by blast
 show ?thesis
 proof (rule lp_answer_contract_modular[where rep="?rep", OF residual initial])
  fix ss t out
  assume rep: "?rep ss t out"
  and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow> ?rep vs v ret \<Longrightarrow>
    lp_answer_contract ?T vs (lp_ild Q) v ret"
  obtain joint swaps j eta where exact: "ss=lpc_attach_answers rest (lpc_reinterface ?R joint)"
  and inv: "J joint"
  and bound: "j<length nds"
  and conditions: "node_conditions j eta"
  and shape: "lpc_return_scope_word swaps (lpc_reinterface ?L joint)=lpc_return_eval eta (states!j)"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) eta"
  and free: "lpc_free_knowledge (set (Fs!j)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!j) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!j)"
  and subject_eq: "t=[(lpcn_pred (nds!j),map eta (lpcn_vars (nds!j)))]"
   using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_premised_functor_rep_def)
  have sn: "SN_on (lp_ild Q) {t}" using rep by simp
  have node: "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned j"
   by (cases "actions!j") (use local boundary bound in auto)
  have descendants: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R child)) (lp_ild Q) u returned"
   if strict: "(t,u)\<in>(lp_ild Q)\<^sup>+"
   and child_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface ?L child) u"
   and child_inv: "J child" for child u
  proof -
   have child_sn: "SN_on (lp_ild Q) {u}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
     (use trancl_into_rtrancl[OF strict] in auto)
   show ?thesis by (rule lower[OF strict]) (use child_rep child_inv child_sn in blast)
  qed
  have result: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R joint)) (lp_ild Q) t returned"
   using node conditions known free observed functors shape inv sn descendants
   unfolding lpp_observer_node_contract_def subject_eq by blast
  show "lp_answer_contract ?T ss (lp_ild Q) t out" using result rep exact by simp
 qed
qed

lemma lpp_observer_empty_node_contract:
 assumes empty: "states!i=[]"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   node_conditions J rest returned i"
proof -
 have scope_empty: "lpc_return_scope_word swaps []=[]" for swaps
  by (induct swaps) (auto split: prod.splits)
 have no_runtime: "runtime=[]"
  if shape: "lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime)=lpc_return_eval eta (states!i)"
  for swaps runtime eta
 proof -
  have reversed: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=[]"
   using arg_cong[OF shape, of "lpc_return_scope_word (rev swaps)"]
   by (simp add: empty lpc_return_eval_def lpc_return_scope_word_inverse scope_empty)
  show ?thesis using reversed by (simp add: lpc_reinterface_def)
 qed
 have contract: "lp_answer_contract (lpp_domain_answers P B U D) [] (lp_ild Q) subject returned" for subject
  by (rule lpp_domain_contract_singletons) simp
 show ?thesis unfolding lpp_observer_node_contract_def
  using no_runtime contract by (fastforce simp: lpc_attach_answers_def lpc_reinterface_def)
qed

ML \<open>
val checked = @{thms lpp_observer_table_contract lpp_observer_silent_contract lpp_observer_empty_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer table assembly" else ();
\<close>
end
