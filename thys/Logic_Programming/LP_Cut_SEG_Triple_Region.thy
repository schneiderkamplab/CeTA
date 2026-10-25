theory LP_Cut_SEG_Triple_Region
  imports LP_Cut_SEG_Triple_Connection LP_Cut_SEG_Control_XML
begin

hide_const (open) NthRoot.root Term.root

definition lpc_triple_position_atom where
  "lpc_triple_position_atom vs a = (fst a,map (lpc_seg_position_template vs) (snd a))"

lemma lpc_triple_position_atom_eval:
  assumes distinct: "distinct vs"
    and variables: "set (lp_atom_vars a) \<subseteq> set vs"
  shows "lp_atom_eval (lpc_triple_position_atom vs a) (lpc_return_env (map Var vs) eta)
    =lp_atom_eval a eta"
  using lpc_seg_position_eval[OF distinct] variables
  by (auto simp: lpc_triple_position_atom_def lp_atom_eval_def lp_atom_vars_def
    intro!: map_cong)

record 'f lpc_triple_region =
  lpctg_control :: "'f lpc_seg_control_data"
  lpctg_free :: "string list list"
  lpctg_connections :: "'f lpc_triple_connection list"
  lpctg_emits :: "(nat * (string * 'f lpc_term) list) list"

definition lpc_triple_check_region where
  "lpc_triple_check_region fuel P D Q roots root region =
    (let data=lpctg_control region; nds=lpcsc_nodes data; nd=lpctr_node root;
         states=lpcsc_states data; Fs=lpctg_free region;
         inp=lpc_triple_position_atom (lpcn_vars nd) (lpctr_input root) in
      nds\<noteq>[] \<and> nds!0=nd \<and> states!0=lpc_triple_root_state root \<and>
      Fs!0=lpctr_free root \<and> distinct (lpcn_vars nd) \<and>
      set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars nd) \<and>
      length (lpctg_connections region)=length nds \<and>
      length (lpctg_emits region)=length nds \<and>
      lpc_seg_ranked_control (lpc_seg_control_rank data) (lpcsc_program data) \<and>
      lpc_seg_free_check_control fuel P (lpcsc_program data) nds states Fs
        (lpcsc_returned data) (lpcsc_arity data) (lpcsc_actions data) \<and>
      list_all (\<lambda>i.
        (lpcsc_actions data!i=None \<longrightarrow>
          lpc_triple_check_connection fuel D Q roots (nds!i) (Fs!i) (states!i) inp
            (lpctr_output root) (lpctg_connections region!i)) \<and>
        lpc_triple_check_emit Q (lpctr_output root) (states!i)
          (fst (lpctg_emits region!i)) (snd (lpctg_emits region!i))) [0..<length nds])"

theorem lpc_triple_region_checked_lower:
  fixes P :: "('f,string) lp_cut_program"
    and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_triple_check_region fuel P D Q roots root region"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpc_triple_root_rep roots us b ret \<Longrightarrow> lpc_triple_answer_contract P us Q ret"
  shows "lpc_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  let ?data = "lpctg_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Fs = "lpctg_free region"
  let ?nd = "lpctr_node root"
  let ?inp = "lpc_triple_position_atom (lpcn_vars ?nd) (lpctr_input root)"
  let ?a = "lp_atom_eval (lpctr_input root) eta"
  let ?ss = "lpc_return_eval eta (lpc_triple_root_state root)"
  have control: "lpc_seg_free_check_control fuel P (lpcsc_program ?data) ?nds ?states ?Fs
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lpcsc_actions ?data)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) (lpcsc_program ?data)"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_triple_root_state root" "?Fs!0=lpctr_free root"
    and distinct: "distinct (lpcn_vars ?nd)"
    and variables: "set (lp_atom_vars (lpctr_input root)) \<subseteq> set (lpcn_vars ?nd)"
    using checked by (auto simp: lpc_triple_check_region_def Let_def)
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var (lpcn_vars ?nd)) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct variables])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_triple_root_state_def lpc_return_eval_def
    by (auto simp: list_all_iff equal intro!: exI[of _ LPIVar])
  have rep: "lpc_return_free_module_rep ?nds ?states ?Fs ?ss
      [(lpcn_pred ?nd,map eta (lpcn_vars ?nd))]"
    unfolding lpc_return_free_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpc_return_free_rep_def,
      rule exI[of _ 0], rule exI[of _ eta])
      (use control nonempty first known free in \<open>auto simp: lpc_seg_free_check_control_def\<close>)
  show ?thesis
  proof (rule lpc_triple_observed_control[OF control ranked program inv rep])
    fix i rho assume index: "i<length ?nds" and boundary_node: "lpcsc_actions ?data!i=None"
      and known': "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) rho"
      and free': "lpc_free_knowledge (set (?Fs!i)) rho"
      and inv': "lpc_triple_instance_invariant ?a ?inp (lpc_return_eval rho (?states!i))"
    have connection: "lpc_triple_check_connection fuel D Q roots (?nds!i) (?Fs!i) (?states!i)
      ?inp (lpctr_output root) (lpctg_connections region!i)"
      using checked index boundary_node by (auto simp: lpc_triple_check_region_def Let_def list_all_iff)
    show "lpc_triple_answer_contract P (lpc_return_eval rho (?states!i)) Q (lp_atom_eval (lpctr_output root))"
      by (rule lpc_triple_connection_checked_lower[OF connection program known' free' inv' lower])
  next
    fix i assume "i<length ?nds"
    then show "lpc_triple_check_emit Q (lpctr_output root) (?states!i)
        (fst (lpctg_emits region!i)) (snd (lpctg_emits region!i))"
      using checked by (auto simp: lpc_triple_check_region_def Let_def list_all_iff)
  qed
qed

end
