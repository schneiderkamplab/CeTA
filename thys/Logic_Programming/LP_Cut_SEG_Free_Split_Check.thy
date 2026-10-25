theory LP_Cut_SEG_Free_Split_Check
  imports LP_Cut_SEG_Split_Check LP_Cut_SEG_Free_Child
begin

definition lpc_seg_free_check_split where
  "lpc_seg_free_check_split fuel (P::('f,string) lp_cut_program) roots Fs entry_root F is_cont c d C R receipt =
    (let nd=lpcsr_node entry_root; vs=lpcn_vars nd; G=lpcn_ground nd;
      pre=lpcss_pre receipt; rest=lpcss_rest receipt; H=lpcss_ground receipt;
      fi=lpcss_first_in receipt; fo=lpcss_first_out receipt;
      si=lpcss_second_in receipt; so=lpcss_second_out receipt; final=lpcss_final receipt;
      u=lpcss_u receipt; v=lpcss_v receipt; caps=lpcss_caps receipt; more=lpcss_more_caps receipt in
     lpcn_state nd=[LPCGoals (pre@rest)] \<and> pre\<noteq>[] \<and> distinct vs \<and>
     lpcsr_output entry_root=lpc_seg_position_template vs final \<and>
     set H \<subseteq> set vs \<and>
     vars_term si \<subseteq> set H \<and>
     vars_term fo \<subseteq> set vs \<and> vars_term (Fun v (si#more)) \<subseteq> set vs \<and>
     vars_term so \<subseteq> set vs \<and> vars_term final \<subseteq> set vs \<and>
     lpc_check_return_route_goals (zip vs [0..<length vs]) (map Var vs :: ('f lp_cut_symbol,string) term list) rest \<and>
     lpc_seg_free_check_child fuel roots Fs pre G F (lpcn_guards nd) vs fi fo (lpcss_first receipt) \<and>
     lpc_seg_free_check_child fuel roots Fs rest H [] [] vs si so (lpcss_second receipt) \<and>
     is_cont u \<and> is_cont v \<and>
     lpc_seg_check_encoded_pair 1 2 is_cont c d C R (lpcsr_input entry_root) (Fun u (fi#caps)) \<and>
     lpc_seg_check_encoded_pair 2 2 is_cont c d C R (Fun u (fo#caps)) (Fun v (si#more)) \<and>
     lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun v (so#more)) final \<and>
     lpc_seg_ground_evidence_check P pre G vs fo (lpcss_prefix_evidence receipt) \<and>
     lpc_seg_ground_evidence_check P pre G vs (Fun LPCTruth (map Var H)) (lpcss_prefix_evidence receipt) \<and>
     lpc_seg_ground_evidence_check P rest H vs so (lpcss_second_evidence receipt))"

theorem lpc_seg_free_split_checked_lower:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_free_check_split fuel P roots Fs entry_root F is_cont c d C R receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpcsr_node entry_root)))
      (lpcn_guards (lpcsr_node entry_root)) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lp_seg_ground (lp_ieval (lpcsr_input entry_root) eta)"
    and lower: "\<And>us v out. (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>,v)
      \<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow> lpc_seg_free_root_rep roots Fs is_cont c d us v out \<Longrightarrow>
      lpc_return_contract P us (qrstep False Q R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lpc_return_contract P (lpc_return_eval eta (lpc_seg_root_state entry_root)) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d (lpcsr_input entry_root) eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpcsr_output entry_root) rho\<rangle>)"
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
  let ?t="A\<langle>lpc_seg_return_value is_cont c d ?l eta\<rangle>"
  let ?rr="qrstep False Q R"
  have state: "lpcn_state ?nd=[LPCGoals (?pre@?rest)]"
    and out: "lpcsr_output entry_root=lpc_seg_position_template ?vs ?final"
    and distinct: "distinct ?vs" and covered: "set ?H \<subseteq> set ?vs"
    and first: "lpc_seg_free_check_child fuel roots Fs ?pre ?G F (lpcn_guards ?nd) ?vs ?fi ?fo (lpcss_first receipt)"
    and second: "lpc_seg_free_check_child fuel roots Fs ?rest ?H [] [] ?vs ?si ?so (lpcss_second receipt)"
    and enter: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R ?l (Fun ?u (?fi#?caps))"
    and cont: "is_cont ?u" "is_cont ?v"
    and vars_si: "vars_term ?si \<subseteq> set ?H"
    using checked
    by (auto simp: lpc_seg_free_check_split_def Let_def)
  have ground: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
    using known by (simp add: lp_cut_knowledge_def)
  have prefix_check: "lpc_seg_check_return_ground P ?pre ?G ?vs ?fo
      (lpcsk_program (lpcss_prefix_evidence receipt))
      (lpcsk_predicates (lpcss_prefix_evidence receipt)) (lpcsk_modes (lpcss_prefix_evidence receipt))"
    and environment_check: "lpc_seg_check_return_ground P ?pre ?G ?vs (Fun LPCTruth (map Var ?H))
      (lpcsk_program (lpcss_prefix_evidence receipt))
      (lpcsk_predicates (lpcss_prefix_evidence receipt)) (lpcsk_modes (lpcss_prefix_evidence receipt))"
    and second_check: "lpc_seg_check_return_ground P ?rest ?H ?vs ?so
      (lpcsk_program (lpcss_second_evidence receipt))
      (lpcsk_predicates (lpcss_second_evidence receipt)) (lpcsk_modes (lpcss_second_evidence receipt))"
    using checked by (auto simp: lpc_seg_free_check_split_def lpc_seg_ground_evidence_check_def Let_def)
  have call: "lp_seg_ground (lp_ieval ?fi eta) \<and>
    (?t,A\<langle>(lpc_seg_pending c d ?u ?caps eta)\<langle>lpc_seg_return_value is_cont c d ?fi eta\<rangle>\<rangle>)\<in>?rr"
    using lpc_seg_checked_call[where Q=Q, OF enter cont(1) finite range roots]
    by (auto simp: lpc_seg_pending_def lpc_seg_return_value_def intro: qrstep.ctxt)
  have prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) ?rr
    (A\<langle>(lpc_seg_pending c d ?u ?caps eta)\<langle>lpc_seg_return_value is_cont c d ?fi eta\<rangle>\<rangle>)
    (\<lambda>rho. A\<langle>(lpc_seg_pending c d ?u ?caps eta)\<langle>
      lpc_seg_return_value is_cont c d (lpc_seg_position_template ?vs ?fo) rho\<rangle>\<rangle>)"
    using lpc_seg_free_child_lower[where A="A\<circ>\<^sub>c lpc_seg_pending c d ?u ?caps eta"
      and t="?t" and is_cont=is_cont and c=c and d=d,
      OF first program known free conjunct1[OF call] lower]
      conjunct2[OF call] by auto
  have environment: "\<forall>x\<in>set ?H. lp_seg_ground (theta x)"
    if actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho"
    and rho: "rho=lpc_return_env (map Var ?vs) theta" for rho theta
    by (rule lpc_seg_return_ground_environment[OF environment_check ground actual distinct covered rho])
  have result: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals (?pre@?rest),map Var ?vs)]) ?rr ?t
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d (lpc_seg_position_template ?vs ?final) rho\<rangle>)"
  proof (rule lpc_seg_split_composition[OF program _ distinct _ enter _ _ cont finite _ _ _ _ prefix _ _ _ range roots])
    show "lpc_check_return_route_goals (zip ?vs [0..<length ?vs]) (map Var ?vs :: ('f lp_cut_symbol,string) term list) ?rest"
      using checked by (simp add: lpc_seg_free_check_split_def Let_def)
    show "?pre\<noteq>[]" using checked by (simp add: lpc_seg_free_check_split_def Let_def)
    show "lpc_seg_check_encoded_pair 2 2 is_cont c d C R (Fun ?u (?fo#?caps)) (Fun ?v (?si#?more))"
      using checked by (simp add: lpc_seg_free_check_split_def Let_def)
    show "lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun ?v (?so#?more)) ?final"
      using checked by (simp add: lpc_seg_free_check_split_def Let_def)
    show "vars_term ?fo \<subseteq> set ?vs" "vars_term (Fun ?v (?si#?more)) \<subseteq> set ?vs"
      "vars_term ?so \<subseteq> set ?vs" "vars_term ?final \<subseteq> set ?vs"
      using checked by (auto simp: lpc_seg_free_check_split_def Let_def)
    show "lp_seg_ground (lp_ieval (lpc_seg_position_template ?vs ?fo) rho)"
      if "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho" for rho
      by (rule lpc_seg_checked_return_ground[OF prefix_check ground that])
  next
    fix rho theta
    assume actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho"
      and rho: "rho=lpc_return_env (map Var ?vs) theta"
      and strict: "(?t,A\<langle>(lpc_seg_pending c d ?v ?more theta)\<langle>
        lpc_seg_return_value is_cont c d ?si theta\<rangle>\<rangle>)\<in>?rr\<^sup>+"
    have known': "lp_cut_knowledge (set ?H) [] theta"
      using environment[OF actual rho] by (simp add: lp_cut_knowledge_def)
    have free': "lpc_free_knowledge (set []) theta" by (simp add: lpc_free_knowledge_def)
    have finite': "lp_seg_ground (lp_ieval ?si theta)"
      using environment[OF actual rho] vars_si by (auto simp: lp_seg_ground_eval)
    show "lpc_return_contract P (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) ?rr
      (A\<langle>(lpc_seg_pending c d ?v ?more theta)\<langle>lpc_seg_return_value is_cont c d ?si theta\<rangle>\<rangle>)
      (\<lambda>sigma. A\<langle>(lpc_seg_pending c d ?v ?more theta)\<langle>
        lpc_seg_return_value is_cont c d (lpc_seg_position_template ?vs ?so) sigma\<rangle>\<rangle>)"
      using lpc_seg_free_child_lower[where A="A\<circ>\<^sub>c lpc_seg_pending c d ?v ?more theta"
        and t="?t" and is_cont=is_cont and c=c and d=d,
        OF second program known' free' finite' lower] strict by auto
  next
    fix rho theta sigma
    assume actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]) rho"
      and rho: "rho=lpc_return_env (map Var ?vs) theta"
      and returned: "lpc_actual_return P (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) sigma"
    show "lp_seg_ground (lp_ieval (lpc_seg_position_template ?vs ?so) sigma)"
      by (rule lpc_seg_checked_return_ground[OF second_check environment[OF actual rho] returned])
  qed
  show ?thesis using result by (simp add: lpc_seg_root_state_def state out)
qed

end
