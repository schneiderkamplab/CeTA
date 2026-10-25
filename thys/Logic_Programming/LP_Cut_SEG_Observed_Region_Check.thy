theory LP_Cut_SEG_Observed_Region_Check
  imports LP_Cut_SEG_Observed_Templates LP_Cut_SEG_Free_Region_Check
begin

definition lpc_seg_check_observed_region where
  "lpc_seg_check_observed_region fuel P roots Fs entry_root F filtering is_cont c d R region Ls =
    (let data=lpcsg_control region; nds=lpcsc_nodes data;
         entries=lpcsg_templates region; nd=lpcsr_node entry_root in
      lpc_seg_free_control_data_check fuel P data Ls \<and> nds\<noteq>[] \<and>
      nds!0=nd \<and> Ls!0=F \<and> lpcsc_states data!0=lpc_seg_root_state entry_root \<and>
      lpcsc_arity data=length (lpcn_vars nd) \<and>
      lpcn_pred nd\<noteq>lpcsc_returned data \<and>
      vars_term (lpcsr_output entry_root) \<subseteq> set [0..<lpcsc_arity data] \<and>
      lpc_seg_check_observer_templates (lpc_seg_position_template (lpcn_vars nd) (lpcsr_input entry_root)) entries nds (lpcsc_states data) \<and>
      map_of entries (lpcn_pred nd)=Some (lpcn_vars nd,lpcsr_input entry_root) \<and>
      lpc_seg_check_observer_emits filtering is_cont c d R
        (lpc_seg_position_template (lpcn_vars nd) (lpcsr_input entry_root)) (lpcsr_output entry_root) (lpcsc_states data) \<and>
      distinct (map fst (lpcsg_connections region)) \<and>
      list_all (\<lambda>i. lpcsc_actions data!i=None \<longrightarrow>
        (case (map_of (lpcsg_connections region) i,map_of entries (lpcn_pred (nds!i))) of
          (Some receipt,Some (vs,l)) \<Rightarrow> vs=lpcn_vars (nds!i) \<and>
            lpc_seg_check_projected_connection fuel P roots Fs filtering is_cont c d R (nds!i) (Ls!i) (lpcsc_states data!i)
              l (lpcsr_output entry_root) receipt
          | _ \<Rightarrow> False)) [0..<length nds])"

theorem lpc_seg_observed_region_checked_lower:
  fixes filtering :: "'g afs"
  assumes checked: "lpc_seg_check_observed_region fuel P roots Fs entry_root F filtering is_cont c d R region Ls"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>vs v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta),v)
        \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      lpc_seg_projected_root_rep filtering roots Fs is_cont c d vs v out \<Longrightarrow>
      lpc_return_contract P vs (lpc_seg_projected_rel filtering R) v out"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))"
proof -
  let ?data = "lpcsg_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Q = "lpcsc_program ?data"
  let ?entries = "lpcsg_templates region"
  let ?templates = "lpc_seg_templates ?entries"
  let ?nd = "lpcsr_node entry_root"
  let ?a = "(lpcn_pred ?nd,map eta (lpcn_vars ?nd))"
  let ?inp = "lpc_seg_position_template (lpcn_vars ?nd) (lpcsr_input entry_root)"
  let ?observed = "lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta"
  have control: "lpc_seg_free_check_control fuel P ?Q ?nds ?states Ls (lpcsc_returned ?data)
      (lpcsc_arity ?data) (lpcsc_actions ?data)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) ?Q"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_seg_root_state entry_root" "Ls!0=F"
    and templates: "lpc_seg_check_observer_templates ?inp ?entries ?nds ?states"
    and lookup: "map_of ?entries (lpcn_pred ?nd)=Some (lpcn_vars ?nd,lpcsr_input entry_root)"
    using checked by (auto simp: lpc_seg_check_observed_region_def lpc_seg_free_control_data_check_def Let_def)
  have initial_vars: "distinct (lpcn_vars ?nd) \<and> vars_term (lpcsr_input entry_root)\<subseteq> set (lpcn_vars ?nd)"
    using templates map_of_SomeD[OF lookup]
    by (auto simp: lpc_seg_check_observer_templates_def list_all_iff)
  obtain m :: "('g,string) term" where origin: "lp_iproject filtering ?observed m"
    using finite by (auto simp: lpc_seg_has_projection_def)
  let ?J="lpc_seg_observer_invariant filtering is_cont c d ?inp m"
  have initial: "?J (lpc_return_eval eta (lpc_seg_root_state entry_root))"
    using origin
    by (simp add: lpc_seg_observer_invariant_def lpc_return_eval_def lpc_seg_root_state_def
      lpc_seg_runtime_value_def lpc_seg_position_eval[OF conjunct1[OF initial_vars] conjunct2[OF initial_vars]]
      list_all_iff split_def)
  have state_length: "length ?states=length ?nds" using control by (simp add: lpc_seg_free_check_control_def)
  have free_length: "length Ls=length ?nds" using control by (simp add: lpc_seg_free_check_control_def)
  have represented: "lpc_return_free_module_rep ?nds ?states Ls
    (lpc_return_eval eta (lpc_seg_root_state entry_root)) [?a]"
    unfolding lpc_return_free_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpc_return_free_rep_def,
        rule exI[of _ 0], rule exI[of _ eta])
      (use nonempty state_length free_length first known free in auto)
  have contract: "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root))
    (lpc_seg_projected_rel filtering R) (A ?observed)
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))"
  proof (rule lpc_seg_observed_control_contract[where J="?J", OF control ranked program initial
    lpc_seg_observer_step lpc_seg_observer_subset lpc_seg_observer_scopes represented])
    fix i nu assume index: "i<length ?nds" and boundary: "lpcsc_actions ?data!i=None"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) nu"
      and local_free: "lpc_free_knowledge (set (Ls!i)) nu"
      and inv: "?J (lpc_return_eval nu (?states!i))"
    have local: "case (map_of (lpcsg_connections region) i,map_of ?entries (lpcn_pred (?nds!i))) of
      (Some receipt,Some (vs,l)) \<Rightarrow> vs=lpcn_vars (?nds!i) \<and>
        lpc_seg_check_projected_connection fuel P roots Fs filtering is_cont c d R (?nds!i) (Ls!i) (?states!i) l (lpcsr_output entry_root) receipt
      | _ \<Rightarrow> False"
      using checked index boundary by (auto simp: lpc_seg_check_observed_region_def Let_def list_all_iff)
    obtain receipt l where receipt_entry: "map_of (lpcsg_connections region) i=Some receipt"
      and entry: "map_of ?entries (lpcn_pred (?nds!i))=Some (lpcn_vars (?nds!i),l)"
      and connection: "lpc_seg_check_projected_connection fuel P roots Fs filtering is_cont c d R (?nds!i) (Ls!i) (?states!i) l (lpcsr_output entry_root) receipt"
    proof -
      obtain receipt where receipt: "map_of (lpcsg_connections region) i=Some receipt"
        using local by (cases "map_of (lpcsg_connections region) i") auto
      obtain vs l where template: "map_of ?entries (lpcn_pred (?nds!i))=Some (vs,l)"
        using local receipt by (cases "map_of ?entries (lpcn_pred (?nds!i))") auto
      have eq: "vs=lpcn_vars (?nds!i)" and check:
        "lpc_seg_check_projected_connection fuel P roots Fs filtering is_cont c d R (?nds!i) (Ls!i) (?states!i) l (lpcsr_output entry_root) receipt"
        using local by (simp_all add: receipt template)
      have entry': "map_of ?entries (lpcn_pred (?nds!i))=Some (lpcn_vars (?nds!i),l)"
        using template eq by simp
      show thesis by (rule that[OF receipt entry' check])
    qed
    have nonempty_state: "?states!i\<noteq>[]"
      using connection by (auto simp: lpc_seg_check_projected_connection_def)
    obtain e obs rest where state: "?states!i=(e,obs)#rest"
      using nonempty_state by (cases "?states!i") auto
    have expected: "map_of ?entries (lpcn_pred (?nds!i)) =
      Some (lpcn_vars (?nds!i),lpc_seg_compose_observation obs ?inp)"
    proof -
      have all: "\<forall>j\<in>set [0..<length ?nds]. case ?states!j of [] \<Rightarrow> True
        | (e,obs)#rest \<Rightarrow> map_of ?entries (lpcn_pred (?nds!j)) =
          Some (lpcn_vars (?nds!j),lpc_seg_compose_observation obs ?inp)"
        using templates by (simp add: lpc_seg_check_observer_templates_def list_all_iff)
      have member: "i\<in>set [0..<length ?nds]" using index by simp
      show ?thesis using all[rule_format, OF member] by (simp only: state) simp
    qed
    have same: "l=lpc_seg_compose_observation obs ?inp" using entry expected by simp
    have shared: "lp_iproject filtering (lpc_seg_runtime_value is_cont c d l nu) m"
      unfolding same by (rule lpc_seg_observer_boundary[OF inv state])
    show "lpc_return_contract P (lpc_return_eval nu (?states!i)) (lpc_seg_projected_rel filtering R)
      (A ?observed) (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))"
      by (rule lpc_seg_projected_connection_checked_lower[OF connection program knowledge local_free origin shared ambient lower])
  next
    fix i nu rho tt assume index: "i<length ?nds"
      and inv: "?J (lpc_return_eval nu (?states!i))"
      and event: "lpc_answer_transition P (lpc_return_eval nu (?states!i)) (Some rho) tt"
    have emits: "lpc_seg_check_observer_emits filtering is_cont c d R ?inp (lpcsr_output entry_root) ?states"
      using checked by (simp add: lpc_seg_check_observed_region_def Let_def)
    have bound: "i<length ?states" using index state_length by simp
    have edge: "(?observed,lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho)
      \<in>lpc_seg_projected_rel filtering R"
      by (rule lpc_seg_observer_emit[OF emits bound inv event origin])
    show "(A ?observed,A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))
      \<in>(lpc_seg_projected_rel filtering R)\<^sup>*"
      by (rule r_into_rtrancl[OF lpc_seg_projection_context_step[OF ambient edge]])
  qed
  show ?thesis by (rule contract)
qed

end
