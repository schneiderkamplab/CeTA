theory LP_Cut_SEG_Region_Check
  imports LP_Cut_SEG_Connection_Check LP_Cut_SEG_Control_XML
begin

record 'f lpc_seg_region =
  lpcsg_control :: "'f lpc_seg_control_data"
  lpcsg_templates :: "('f lp_cut_symbol * string list * 'f lpc_term) list"
  lpcsg_connections :: "(nat * 'f lpc_seg_connection) list"

definition lpc_seg_check_region where
  "lpc_seg_check_region fuel P roots entry_root is_cont c d C R region =
    (let data=lpcsg_control region; nds=lpcsc_nodes data;
         entries=lpcsg_templates region; nd=lpcsr_node entry_root in
      lpc_seg_control_data_check fuel P data \<and> nds\<noteq>[] \<and>
      nds!0=nd \<and> lpcsc_states data!0=lpc_seg_root_state entry_root \<and>
      lpcsc_arity data=length (lpcn_vars nd) \<and>
      lpcn_pred nd\<noteq>lpcsc_returned data \<and>
      vars_term (lpcsr_output entry_root) \<subseteq> set [0..<lpcsc_arity data] \<and>
      lpc_seg_check_templates entries (lpcsc_program data) \<and>
      map_of entries (lpcn_pred nd)=Some (lpcn_vars nd,lpcsr_input entry_root) \<and>
      lpc_seg_check_encoded_emits (lpc_seg_templates entries) (lpcsc_returned data)
        (lpcsr_output entry_root) is_cont c d C R (lpcsc_program data) \<and>
      distinct (map fst (lpcsg_connections region)) \<and>
      list_all (\<lambda>i. lpcsc_actions data!i=None \<longrightarrow>
        (case (map_of (lpcsg_connections region) i,map_of entries (lpcn_pred (nds!i))) of
          (Some receipt,Some (vs,l)) \<Rightarrow> vs=lpcn_vars (nds!i) \<and>
            lpc_seg_check_connection P roots is_cont c d C R (nds!i) (lpcsc_states data!i)
              l (lpcsr_output entry_root) receipt
          | _ \<Rightarrow> False)) [0..<length nds])"

theorem lpc_seg_region_checked_lower:
  assumes checked: "lpc_seg_check_region fuel P roots entry_root is_cont c d C R region"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input entry_root) eta)"
    and lower: "\<And>vs v out. (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>,v)
        \<in>(qrstep False N R)\<^sup>+ \<Longrightarrow>
      lpc_seg_root_rep roots is_cont c d vs v out \<Longrightarrow>
      lpc_return_contract P vs (qrstep False N R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>N \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (qrstep False N R)
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
proof -
  let ?data = "lpcsg_control region"
  let ?nds = "lpcsc_nodes ?data"
  let ?states = "lpcsc_states ?data"
  let ?Q = "lpcsc_program ?data"
  let ?entries = "lpcsg_templates region"
  let ?templates = "lpc_seg_templates ?entries"
  let ?nd = "lpcsr_node entry_root"
  let ?a = "(lpcn_pred ?nd,map eta (lpcn_vars ?nd))"
  let ?measure = "lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lpc_seg_template_value ?templates ?a))"
  have control: "lpc_seg_check_control fuel P ?Q ?nds ?states (lpcsc_returned ?data)
      (lpcsc_arity ?data) (lpcsc_actions ?data)"
    and ranked: "lpc_seg_ranked_control (lpc_seg_control_rank ?data) ?Q"
    and nonempty: "?nds\<noteq>[]"
    and first: "?nds!0=?nd" "?states!0=lpc_seg_root_state entry_root"
    and templates: "lpc_seg_check_templates ?entries ?Q"
    and lookup: "map_of ?entries (lpcn_pred ?nd)=Some (lpcn_vars ?nd,lpcsr_input entry_root)"
    using checked by (auto simp: lpc_seg_check_region_def lpc_seg_control_data_check_def Let_def)
  have initial_vars: "distinct (lpcn_vars ?nd) \<and> vars_term (lpcsr_input entry_root) \<subseteq> set (lpcn_vars ?nd)"
    by (rule lpc_seg_template_lookup_valid[OF templates lookup])
  have initial_equal: "lpc_seg_template_value ?templates ?a=lp_ieval (lpcsr_input entry_root) eta"
    by (rule lpc_seg_input_template[where templates="?templates" and pred="lpcn_pred ?nd", OF conjunct1[OF initial_vars] conjunct2[OF initial_vars]
      lpc_seg_template_lookup[OF lookup]])
  have measured: "lp_seg_ground (lpc_seg_template_value ?templates ?a)"
    using finite initial_equal by simp
  have state_length: "length ?states=length ?nds" using control by (simp add: lpc_seg_check_control_def)
  have represented: "lpc_return_module_rep ?nds ?states
    (lpc_return_eval eta (lpc_seg_root_state entry_root)) [?a]"
    unfolding lpc_return_module_rep_def
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps lpc_return_rep_def,
        rule exI[of _ 0], rule exI[of _ eta])
      (use nonempty state_length first known in auto)
  have contract: "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (qrstep False N R)
    (A\<langle>?measure\<rangle>) (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
  proof (rule lpc_seg_context_region_contract[OF control ranked program represented _ _ _ measured _ range roots])
    show "lpc_seg_template_program_on (set (map fst ?entries)) ?templates ?Q"
      using templates by (simp add: lpc_seg_check_templates_def)
    show "lpc_seg_check_encoded_emits ?templates (lpcsc_returned ?data) (lpcsr_output entry_root) is_cont c d C R ?Q"
      using checked by (simp add: lpc_seg_check_region_def Let_def)
    show "fst ?a\<noteq>lpcsc_returned ?data"
      using checked by (simp add: lpc_seg_check_region_def Let_def)
    show "vars_term (lpcsr_output entry_root) \<subseteq> set [0..<lpcsc_arity ?data]"
      using checked by (auto simp: lpc_seg_check_region_def Let_def)
  next
    fix i nu assume index: "i<length ?nds" and boundary: "lpcsc_actions ?data!i=None"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (?nds!i))) (lpcn_guards (?nds!i)) nu"
      and path: "([?a],[(lpcn_pred (?nds!i),map nu (lpcn_vars (?nds!i)))])\<in>(lp_ild ?Q)\<^sup>*"
    have local: "case (map_of (lpcsg_connections region) i,map_of ?entries (lpcn_pred (?nds!i))) of
      (Some receipt,Some (vs,l)) \<Rightarrow> vs=lpcn_vars (?nds!i) \<and>
        lpc_seg_check_connection P roots is_cont c d C R (?nds!i) (?states!i) l (lpcsr_output entry_root) receipt
      | _ \<Rightarrow> False"
      using checked index boundary by (auto simp: lpc_seg_check_region_def Let_def list_all_iff)
    obtain receipt l where receipt_entry: "map_of (lpcsg_connections region) i=Some receipt"
      and entry: "map_of ?entries (lpcn_pred (?nds!i))=Some (lpcn_vars (?nds!i),l)"
      and connection: "lpc_seg_check_connection P roots is_cont c d C R (?nds!i) (?states!i) l (lpcsr_output entry_root) receipt"
    proof -
      obtain receipt where receipt: "map_of (lpcsg_connections region) i=Some receipt"
        using local by (cases "map_of (lpcsg_connections region) i") auto
      obtain vs l where template: "map_of ?entries (lpcn_pred (?nds!i))=Some (vs,l)"
        using local receipt by (cases "map_of ?entries (lpcn_pred (?nds!i))") auto
      have eq: "vs=lpcn_vars (?nds!i)" and check:
        "lpc_seg_check_connection P roots is_cont c d C R (?nds!i) (?states!i) l (lpcsr_output entry_root) receipt"
        using local by (simp_all add: receipt template)
      have entry': "map_of ?entries (lpcn_pred (?nds!i))=Some (lpcn_vars (?nds!i),l)"
        using template eq by simp
      show thesis by (rule that[OF receipt entry' check])
    qed
    have valid: "distinct (lpcn_vars (?nds!i)) \<and> vars_term l \<subseteq> set (lpcn_vars (?nds!i))"
      by (rule lpc_seg_template_lookup_valid[OF templates entry])
    have current: "lpc_seg_template_value ?templates (lpcn_pred (?nds!i),map nu (lpcn_vars (?nds!i)))=lp_ieval l nu"
      by (rule lpc_seg_input_template[where templates="?templates" and pred="lpcn_pred (?nds!i)", OF conjunct1[OF valid] conjunct2[OF valid] lpc_seg_template_lookup[OF entry]])
    have same: "lp_ieval l nu=lpc_seg_template_value ?templates ?a"
      using lpc_seg_checked_template_path[OF templates path measured]
        lpc_seg_template_lookup_active[OF entry]
      by (simp add: current)
    have local_finite: "lp_seg_ground (lp_ieval l nu)" using measured same by simp
    have local_lower: "lpc_return_contract P us (qrstep False N R) v out"
      if strict: "(A\<langle>lpc_seg_return_value is_cont c d l nu\<rangle>,v)\<in>(qrstep False N R)\<^sup>+"
      and rep: "lpc_seg_root_rep roots is_cont c d us v out" for us v out
      by (rule lower[OF _ rep]) (use strict in \<open>simp only: lpc_seg_return_value_def same initial_equal\<close>)
    have child: "lpc_return_contract P (lpc_return_eval nu (?states!i)) (qrstep False N R)
      (A\<langle>lpc_seg_return_value is_cont c d l nu\<rangle>)
      (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
      by (rule lpc_seg_connection_checked_lower[OF connection program knowledge local_finite local_lower range roots])
    show "lpc_return_contract P (lpc_return_eval nu (?states!i)) (qrstep False N R)
      (A\<langle>?measure\<rangle>) (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
      using child by (simp only: lpc_seg_return_value_def same)
  qed
  show ?thesis using contract by (simp only: lpc_seg_return_value_def initial_equal)
qed

end
