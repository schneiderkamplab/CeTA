theory LP_Prolog_Context_Regions
 imports LP_Prolog_Context_Region
begin

definition lpp_check_context_regions where
  "lpp_check_context_regions fuel P D T roots regions =
    (lp_cut_source_program P \<and> roots\<noteq>[] \<and> length roots=length regions \<and>
      list_all (\<lambda>i. lpp_check_context_region fuel P D T roots (roots!i) (regions!i)) [0..<length roots])"

theorem lpp_context_regions_SN:
  fixes P :: "(string,string) lp_cut_program" and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_check_context_regions fuel P D T roots regions"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN (lpp_observed_calls (set D) SP :: string lpp_success_iatom rel)"
    and index: "i<length roots"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!i)))) (lpcn_guards (lpctr_node (roots!i))) eta"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {lp_cut_state_eval (lpcn_state (lpctr_node (roots!i))) eta}"
proof -
  have all: "\<forall>j rho. j<length roots \<longrightarrow>
    lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!j)))) (lpcn_guards (lpctr_node (roots!j))) rho \<longrightarrow>
    a=lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!j))) rho \<longrightarrow>
    SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      {lp_cut_state_eval (lpcn_state (lpctr_node (roots!j))) rho}" for a :: "string lpp_success_iatom"
  proof (rule SN_on_induct[OF sn UNIV_I], intro allI impI)
    fix a j rho
    assume ih: "\<And>b. (a,b)\<in>lpp_observed_calls (set D) SP \<Longrightarrow>
      \<forall>k sigma. k<length roots \<longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!k)))) (lpcn_guards (lpctr_node (roots!k))) sigma \<longrightarrow>
      b=lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!k))) sigma \<longrightarrow>
      SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        {lp_cut_state_eval (lpcn_state (lpctr_node (roots!k))) sigma}"
      and j: "j<length roots"
      and known_j: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!j)))) (lpcn_guards (lpctr_node (roots!j))) rho"
      and a: "a=lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!j))) rho"
    have region: "lpp_check_context_region fuel P D T roots (roots!j) (regions!j)"
      and program: "lp_cut_source_program P"
      using checked j by (auto simp: lpp_check_context_regions_def list_all_iff)
    show "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
      {lp_cut_state_eval (lpcn_state (lpctr_node (roots!j))) rho}"
    proof (rule lpp_context_region_checked_lower[OF region program transfer known_j])
      fix k sigma
      assume k: "k<length roots"
        and known_k: "lp_cut_knowledge (set (lpcn_ground (lpctr_node (roots!k)))) (lpcn_guards (lpctr_node (roots!k))) sigma"
        and edge: "(lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!j))) rho,
          lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!k))) sigma)\<in>lpp_observed_calls (set D) SP"
      have edge': "(a,lpp_success_atom_eval (lpp_unlift_atom (lpctr_input (roots!k))) sigma)\<in>lpp_observed_calls (set D) SP"
        using edge by (simp only: a)
      show "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        {lp_cut_state_eval (lpcn_state (lpctr_node (roots!k))) sigma}"
        using ih[OF edge'] k known_k by blast
    qed
  qed
  show ?thesis using all index known by blast
qed

definition lpp_check_context_regions_query where
  "lpp_check_context_regions_query fuel P D T roots regions q modes =
    (lpp_check_context_regions fuel P D T roots regions \<and>
      (let nd=lpctr_node (roots!0) in
        lp_cut_check_root q modes (lpcn_vars nd) (lpcn_state nd) (lpcn_ground nd) (lpcn_guards nd)))"

theorem lpp_context_regions_query_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lpp_check_context_regions_query fuel P D T roots regions q modes"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and sn: "SN (lpp_observed_calls (set D) SP :: string lpp_success_iatom rel)"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?nd = "lpctr_node (roots!0)"
  let ?vs = "lpcn_vars ?nd"
  let ?eta = "lp_cut_query_env ?vs ts"
  have regions: "lpp_check_context_regions fuel P D T roots regions"
    and nonempty: "roots\<noteq>[]"
    and root_check: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    using checked by (auto simp: lpp_check_context_regions_query_def lpp_check_context_regions_def Let_def)
  have lengths: "length ?vs=length ts" and distinct: "distinct ?vs"
    using root_check len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?eta ?vs=ts" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_values: "\<forall>(t,b)\<in>set (zip (map ?eta ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    using root_check finite_values by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have source: "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {lp_cut_state_eval (lpcn_state ?nd) ?eta}"
    by (rule lpp_context_regions_SN[OF regions transfer sn _ known]) (use nonempty in simp)
  show ?thesis using source root_check vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed

ML \<open>
val checked = [@{thm lpp_context_regions_SN}, @{thm lpp_context_regions_query_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual regions dependency" else ();
\<close>
end
