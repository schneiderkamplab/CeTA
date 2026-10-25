theory LP_Cut_SEG_Triple_Receipt
  imports LP_Cut_SEG_Triple_Answers LP_Cut_SEG_Instance
begin

text \<open>Executable successful-answer receipts. A receipt selects a real
supporting clause and a finite substitution. Its entire instantiated body must
be among the supplied facts; no omitted premise or external model is trusted.\<close>

definition lpc_triple_model_subst where
  "lpc_triple_model_subst head bindings x =
    (case map_of bindings x of None \<Rightarrow> Fun (fst head) [] | Some t \<Rightarrow> t)"

definition lpc_triple_check_model_clause where
  "lpc_triple_check_model_clause Q facts head c bindings =
    (c<length Q \<and>
      lp_atom_subst (fst (Q!c)) (lpc_triple_model_subst head bindings)=head \<and>
      list_all (\<lambda>b. lp_atom_subst b (lpc_triple_model_subst head bindings)\<in>set facts)
        (snd (Q!c)))"

lemma lpc_triple_checked_model_clause:
  assumes checked: "lpc_triple_check_model_clause Q facts head c bindings"
    and facts: "\<And>b. b\<in>set facts \<Longrightarrow> lp_answer_model Q (lp_atom_eval b eta)"
  shows "lp_answer_model Q (lp_atom_eval head eta)"
proof -
  let ?mu = "lpc_triple_model_subst head bindings"
  have index: "c<length Q"
    and head: "lp_atom_subst (fst (Q!c)) ?mu=head"
    and body: "\<And>b. b\<in>set (snd (Q!c)) \<Longrightarrow> lp_atom_subst b ?mu\<in>set facts"
    using checked by (auto simp: lpc_triple_check_model_clause_def list_all_iff)
  have eval: "lp_atom_eval (lp_atom_subst b ?mu) eta =
    lp_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta)" for b
    by (simp add: lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have model: "lp_answer_model Q (lp_atom_eval (fst (Q!c)) (\<lambda>x. lp_ieval (?mu x) eta))"
  proof (rule lp_answer_model.clause[OF index])
    fix b assume member: "b\<in>set (snd (Q!c))"
    show "lp_answer_model Q (lp_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta))"
      using facts[OF body[OF member]] by (simp only: eval)
  qed
  have equal: "lp_atom_eval (lp_atom_subst (fst (Q!c)) ?mu) eta=lp_atom_eval head eta"
    by (rule arg_cong[OF head])
  show ?thesis using model equal by (simp only: eval)
qed

definition lpc_triple_observe_atom where
  "lpc_triple_observe_atom templates a =
    (fst a,map (lpc_seg_compose_observation templates) (snd a))"

lemma lpc_triple_observe_atom_eval:
  "lp_atom_eval a (lpc_seg_observe templates eta) =
    lp_atom_eval (lpc_triple_observe_atom templates a) eta"
  by (simp add: lpc_triple_observe_atom_def lp_atom_eval_def
    lpc_seg_observation_eval map_map o_def)

definition lpc_triple_check_call where
  "lpc_triple_check_call D facts head call c bindings =
    (c<length D \<and> (case D!c of (h,ps,b) \<Rightarrow>
      lp_atom_subst h (lpc_triple_model_subst head bindings)=head \<and>
      lp_atom_subst b (lpc_triple_model_subst head bindings)=call \<and>
      list_all (\<lambda>p. lp_atom_subst p (lpc_triple_model_subst head bindings)\<in>set facts) ps))"

theorem lpc_triple_checked_call:
  assumes checked: "lpc_triple_check_call D facts head call c bindings"
    and matching: "lp_iatom_subst a sigma=lp_atom_eval head eta"
    and facts: "\<And>b. b\<in>set facts \<Longrightarrow> lp_answer_model Q (lp_atom_eval b eta)"
  shows "(a,lp_atom_eval call eta)\<in>lp_triple_calls (set D) Q"
proof -
  let ?mu = "lpc_triple_model_subst head bindings"
  obtain h ps b where triple: "D!c=(h,ps,b)" by (cases "D!c") auto
  have index: "c<length D"
    and head: "lp_atom_subst h ?mu=head"
    and call: "lp_atom_subst b ?mu=call"
    and prefix: "\<And>p. p\<in>set ps \<Longrightarrow> lp_atom_subst p ?mu\<in>set facts"
    using checked by (auto simp: lpc_triple_check_call_def triple list_all_iff)
  have eval: "lp_atom_eval (lp_atom_subst p ?mu) eta =
    lp_atom_eval p (\<lambda>x. lp_ieval (?mu x) eta)" for p
    by (simp add: lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have member: "(h,ps,b)\<in>set D" using nth_mem[OF index] triple by simp
  have head_eval: "lp_atom_eval (lp_atom_subst h ?mu) eta=lp_atom_eval head eta"
    by (rule arg_cong[OF head])
  have match: "lp_iatom_subst a sigma=lp_atom_eval h (\<lambda>x. lp_ieval (?mu x) eta)"
    using matching head_eval by (simp only: eval)
  have edge: "(a,lp_atom_eval b (\<lambda>x. lp_ieval (?mu x) eta))\<in>lp_triple_calls (set D) Q"
  proof (rule lp_triple_calls_modelI[OF member match])
    fix p assume member: "p\<in>set ps"
    show "lp_answer_model Q (lp_atom_eval p (\<lambda>x. lp_ieval (?mu x) eta))"
      using facts[OF prefix[OF member]] by (simp only: eval)
  qed
  show ?thesis using edge by (simp only: call[symmetric] eval)
qed

definition lpc_triple_check_instance_answer where
  "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma =
    (lpc_triple_observe_atom
        (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_out =
      lpc_triple_observe_atom (map (lpc_seg_position_template vs) observed) parent_out \<or>
      lpc_triple_check_model_clause Q
        [lpc_triple_observe_atom
          (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_out]
        (lpc_triple_observe_atom (map (lpc_seg_position_template vs) observed) parent_out) c sigma)"

lemma lpc_triple_checked_instance_answer:
  assumes receipt: "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma"
    and model: "lp_answer_model Q (lp_atom_eval child_out
      (lpc_seg_observe (map (lpc_seg_position_template vs)
        (map (lp_cut_instance_subst bindings) child_vars)) rho))"
  shows "lp_answer_model Q (lp_atom_eval parent_out
    (lpc_seg_observe (map (lpc_seg_position_template vs) observed) rho))"
proof -
  let ?child = "lpc_triple_observe_atom
    (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) child_out"
  let ?parent = "lpc_triple_observe_atom (map (lpc_seg_position_template vs) observed) parent_out"
  have child_model: "lp_answer_model Q (lp_atom_eval ?child rho)"
    using model by (simp only: lpc_triple_observe_atom_eval)
  have "?child=?parent \<or> lpc_triple_check_model_clause Q [?child] ?parent c sigma"
    using receipt by (simp add: lpc_triple_check_instance_answer_def Let_def)
  then have "lp_answer_model Q (lp_atom_eval ?parent rho)"
    using child_model lpc_triple_checked_model_clause[where facts="[?child]" and head="?parent"
      and Q=Q and c=c and bindings=sigma and eta=rho] by auto
  then show ?thesis by (simp only: lpc_triple_observe_atom_eval)
qed

theorem lpc_triple_checked_instance_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes inst: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and receipt: "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma"
    and child_contract: "lpc_triple_answer_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) Q (lp_atom_eval child_out)"
  shows "lpc_triple_answer_contract P (lpc_return_eval eta [(e,observed)]) Q (lp_atom_eval parent_out)"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  let ?outputs = "map ?mu child_vars"
  let ?cf = "lpc_seg_observe (map (lpc_seg_position_template vs) ?outputs)"
  let ?pf = "lpc_seg_observe (map (lpc_seg_position_template vs) observed)"
  let ?ss = "lpc_return_eval eta [(e,map Var vs)]"
  have distinct: "distinct vs"
    and out_vars: "\<And>x. x\<in>set ?outputs \<Longrightarrow> vars_term x \<subseteq> set vs"
    and obs_vars: "\<And>x. x\<in>set observed \<Longrightarrow> vars_term x \<subseteq> set vs"
    and annotated: "[(e,?outputs)] = lpc_return_scope_word swaps
      (lpc_return_map (\<lambda>t. t\<cdot>?mu) [(child,map Var child_vars)])"
    using inst by (auto simp: lpc_seg_check_instance_boundary_def Let_def list_all_iff)
  have scoped: "lpc_triple_answer_contract P
    (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])) Q (lp_atom_eval child_out)"
    unfolding lpc_triple_answer_contract_return_contract
    by (rule lpc_return_contract_scopes[OF program])
      (use child_contract in \<open>simp only: lpc_triple_answer_contract_return_contract\<close>)
  have same: "lpc_return_eval eta [(e,?outputs)] =
    lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child': "lpc_triple_answer_contract P (lpc_reinterface ?cf ?ss) Q (lp_atom_eval child_out)"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "lpc_triple_answer_contract P (lpc_reinterface ?pf ?ss) Q (lp_atom_eval parent_out)"
  proof (rule lpc_triple_answer_boundary[OF lpc_seg_observe_commutes lpc_seg_observe_commutes child'])
    fix rho assume child_model: "lp_answer_model Q (lp_atom_eval child_out (?cf rho))"
    show "lp_answer_model Q (lp_atom_eval parent_out (?pf rho))"
      by (rule lpc_triple_checked_instance_answer[OF receipt child_model])
  qed
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed

end
