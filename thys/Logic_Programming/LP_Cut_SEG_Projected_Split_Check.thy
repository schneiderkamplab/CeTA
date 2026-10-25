theory LP_Cut_SEG_Projected_Split_Check
  imports LP_Cut_SEG_Projected_Split_Composition LP_Cut_SEG_Free_Split_Check
begin

definition lpc_seg_check_projected_split where
  "lpc_seg_check_projected_split fuel (P::('f,string) lp_cut_program) roots Fs entry_root F filtering is_cont c d R receipt =
    (let nd=lpcsr_node entry_root; vs=lpcn_vars nd; G=lpcn_ground nd;
      pre=lpcss_pre receipt; rest=lpcss_rest receipt; H=lpcss_ground receipt;
      fi=lpcss_first_in receipt; fo=lpcss_first_out receipt;
      si=lpcss_second_in receipt; so=lpcss_second_out receipt; final=lpcss_final receipt;
      u=lpcss_u receipt; v=lpcss_v receipt; caps=lpcss_caps receipt; more=lpcss_more_caps receipt in
     lpcn_state nd=[LPCGoals (pre@rest)] \<and> pre\<noteq>[] \<and> distinct vs \<and>
     lpcsr_output entry_root=lpc_seg_position_template vs final \<and>
     set H \<subseteq> set vs \<and>
     vars_term fo \<subseteq> set vs \<and> vars_term (Fun v (si#more)) \<subseteq> set vs \<and>
     vars_term so \<subseteq> set vs \<and> vars_term final \<subseteq> set vs \<and>
     lpc_check_return_route_goals (zip vs [0..<length vs]) (map Var vs :: ('f lp_cut_symbol,string) term list) rest \<and>
     lpc_seg_free_check_child fuel roots Fs pre G F (lpcn_guards nd) vs fi fo (lpcss_first receipt) \<and>
     lpc_seg_free_check_child fuel roots Fs rest H [] [] vs si so (lpcss_second receipt) \<and>
     is_cont u \<and> is_cont v \<and>
     lpc_seg_projected_continuation_filter filtering (c u) (Suc (length caps)) \<and>
     lpc_seg_projected_continuation_filter filtering (c v) (Suc (length more)) \<and>
     lpc_seg_check_projected_pair filtering 1 2 is_cont c d R (lpcsr_input entry_root) (Fun u (fi#caps)) \<and>
     lpc_seg_check_projected_pair filtering 2 2 is_cont c d R (Fun u (fo#caps)) (Fun v (si#more)) \<and>
     lpc_seg_check_projected_pair filtering 2 1 is_cont c d R (Fun v (so#more)) final \<and>
     lpc_seg_ground_evidence_check P pre G vs (Fun LPCTruth (map Var H)) (lpcss_prefix_evidence receipt))"

theorem lpc_seg_projected_split_checked_lower:
  fixes P :: "('f,string) lp_cut_program" and filtering :: "'g afs"
  assumes checked: "lpc_seg_check_projected_split fuel P roots Fs entry_root F filtering is_cont c d R receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta)"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>us v out. (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta),v)
      \<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      lpc_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
      lpc_return_contract P us (lpc_seg_projected_rel filtering R) v out"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (lpc_seg_projected_rel filtering R)
    (A (lpc_seg_runtime_value is_cont c d (lpcsr_input entry_root) eta))
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpcsr_output entry_root) rho))"
proof -
  let ?nd="lpcsr_node entry_root"
  let ?vs="lpcn_vars ?nd"
  let ?G="lpcn_ground ?nd"
  let ?H="lpcss_ground receipt"
  let ?pre="lpcss_pre receipt"
  let ?rest="lpcss_rest receipt"
  let ?fi="lpcss_first_in receipt"
  let ?fo="lpcss_first_out receipt"
  let ?si="lpcss_second_in receipt"
  let ?so="lpcss_second_out receipt"
  let ?u="lpcss_u receipt"
  let ?v="lpcss_v receipt"
  let ?caps="lpcss_caps receipt"
  let ?more="lpcss_more_caps receipt"
  let ?final="lpcss_final receipt"
  let ?l="lpcsr_input entry_root"
  let ?t="A (lpc_seg_runtime_value is_cont c d ?l eta)"
  let ?rr="lpc_seg_projected_rel filtering R"
  have state: "lpcn_state ?nd=[LPCGoals (?pre@?rest)]"
    and out: "lpcsr_output entry_root=lpc_seg_position_template ?vs ?final"
    and distinct: "distinct ?vs" and covered: "set ?H \<subseteq> set ?vs"
    and first: "lpc_seg_free_check_child fuel roots Fs ?pre ?G F (lpcn_guards ?nd) ?vs ?fi ?fo (lpcss_first receipt)"
    and second: "lpc_seg_free_check_child fuel roots Fs ?rest ?H [] [] ?vs ?si ?so (lpcss_second receipt)"
    and enter: "lpc_seg_check_projected_pair filtering 1 2 is_cont c d R ?l (Fun ?u (?fi#?caps))"
    and cont: "is_cont ?u" "is_cont ?v"
    and keep: "lpc_seg_projected_continuation_filter filtering (c ?u) (Suc (length ?caps))"
      "lpc_seg_projected_continuation_filter filtering (c ?v) (Suc (length ?more))"
    using checked
    by (auto simp: lpc_seg_check_projected_split_def Let_def)
  have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
    using known by (simp add: lp_cut_knowledge_def)
  have environment_check: "lpc_seg_check_return_ground P ?pre ?G ?vs (Fun LPCTruth (map Var ?H))
      (lpcsk_program (lpcss_prefix_evidence receipt))
      (lpcsk_predicates (lpcss_prefix_evidence receipt)) (lpcsk_modes (lpcss_prefix_evidence receipt))"
    using checked by (auto simp: lpc_seg_check_projected_split_def lpc_seg_ground_evidence_check_def Let_def)
  let ?D="lpc_seg_runtime_pending c d ?u ?caps eta"
  have call: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d ?fi eta) \<and>
    lpc_seg_projection_context filtering (\<lambda>x. A (?D x)) \<and>
    (?t,A (?D (lpc_seg_runtime_value is_cont c d ?fi eta)))\<in>?rr"
    using lpc_seg_projected_call[OF enter cont(1) keep(1) finite ambient]
    by (auto simp: lpc_seg_runtime_pending_def)
  have prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) ?rr
    (A (?D (lpc_seg_runtime_value is_cont c d ?fi eta)))
    (\<lambda>rho. A (?D (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template ?vs ?fo) rho)))"
    by (rule lpc_seg_projected_child_lower[OF first program known free conjunct1[OF call]
      conjunct1[OF conjunct2[OF call]] lower r_into_trancl[OF conjunct2[OF conjunct2[OF call]]]])
  have environment: "\<forall>x\<in>set ?H. lp_seg_ground (theta x)"
    if actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho"
    and rho: "rho=lpc_return_env (map Var ?vs) theta" for rho theta
    by (rule lpc_seg_return_ground_environment[OF environment_check ground actual distinct covered rho])
  have result: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals (?pre@?rest),map Var ?vs)]) ?rr ?t
    (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template ?vs ?final) rho))"
  proof (rule lpc_seg_projected_split_composition[OF program _ distinct _ enter _ _ cont keep finite ambient _ _ _ _ prefix])
    show "lpc_check_return_route_goals (zip ?vs [0..<length ?vs]) (map Var ?vs :: ('f lp_cut_symbol,string) term list) ?rest"
      using checked by (simp add: lpc_seg_check_projected_split_def Let_def)
    show "?pre\<noteq>[]" using checked by (simp add: lpc_seg_check_projected_split_def Let_def)
    show "lpc_seg_check_projected_pair filtering 2 2 is_cont c d R (Fun ?u (?fo#?caps)) (Fun ?v (?si#?more))"
      using checked by (simp add: lpc_seg_check_projected_split_def Let_def)
    show "lpc_seg_check_projected_pair filtering 2 1 is_cont c d R (Fun ?v (?so#?more)) ?final"
      using checked by (simp add: lpc_seg_check_projected_split_def Let_def)
    show "vars_term ?fo \<subseteq> set ?vs" "vars_term (Fun ?v (?si#?more)) \<subseteq> set ?vs"
      "vars_term ?so \<subseteq> set ?vs" "vars_term ?final \<subseteq> set ?vs"
      using checked by (auto simp: lpc_seg_check_projected_split_def Let_def)
  next
    fix rho theta
    assume actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho"
      and rho: "rho=lpc_return_env (map Var ?vs) theta"
      and strict: "(?t,A (lpc_seg_runtime_pending c d ?v ?more theta
        (lpc_seg_runtime_value is_cont c d ?si theta)))\<in>?rr\<^sup>+"
      and finite': "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d ?si theta)"
      and ambient': "lpc_seg_projection_context filtering (\<lambda>x. A (lpc_seg_runtime_pending c d ?v ?more theta x))"
    have known': "lp_cut_knowledge (set ?H) [] theta"
      using environment[OF actual rho] by (simp add: lp_cut_knowledge_def)
    have free': "lpc_free_knowledge (set []) theta" by (simp add: lpc_free_knowledge_def)
    show "lpc_return_contract P (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) ?rr
      (A (lpc_seg_runtime_pending c d ?v ?more theta (lpc_seg_runtime_value is_cont c d ?si theta)))
      (\<lambda>sigma. A (lpc_seg_runtime_pending c d ?v ?more theta
        (lpc_seg_runtime_value is_cont c d (lpc_seg_position_template ?vs ?so) sigma)))"
      by (rule lpc_seg_projected_child_lower[OF second program known' free' finite' ambient' lower strict])
  qed
  show ?thesis using result by (simp add: lpc_seg_root_state_def state out)
qed

end
