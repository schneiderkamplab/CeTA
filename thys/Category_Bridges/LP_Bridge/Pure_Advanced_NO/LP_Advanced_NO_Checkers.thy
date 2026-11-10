theory LP_Advanced_NO_Checkers
  imports LP_Finite_Affine_Loop
begin

theorem check_lp_recurrent_pair_xml_finite_sound:
  assumes parsed: "parse_xml_string lp_recurrent_pair_parser xml =
    Right (P,(q,arity,positions),A,C,x,y,s,d,n,m,a,b,c,keep,steps1,steps2)"
    and ok: "check_lp_recurrent_pair_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
  by (rule lp_finite_recurrent_pair_check_sound)
    (use parsed ok in \<open>simp add: check_lp_recurrent_pair_xml_def\<close>)

theorem check_lp_pattern_loop_xml_finite_sound:
  assumes parsed: "parse_xml_string lp_pattern_loop_parser xml =
    Right (P,(q,arity,positions),A,sig,mu,firststeps,steps,acc)"
    and ok: "check_lp_pattern_loop_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof (cases acc)
  case None
  show ?thesis by (rule lp_finite_pattern_loop_check_sound)
    (use parsed ok None in \<open>simp add: check_lp_pattern_loop_xml_def\<close>)
next
  case (Some witness)
  obtain B ls lm theta eta delta k b where witness: "witness=(B,ls,lm,theta,eta,delta,k,b)"
    by (cases witness) auto
  have checked: "lp_accelerated_loop_check P q arity positions A sig mu firststeps steps B ls lm theta eta delta k b"
    using parsed ok Some witness by (simp add: check_lp_pattern_loop_xml_def)
  show ?thesis by (rule lp_finite_accelerated_loop_check_sound[OF checked])
qed

theorem check_lp_affine_loop_xml_finite_sound:
  assumes parsed: "parse_xml_string lp_affine_loop_parser xml =
    Right (P,(q,arity,positions),c,z,env,A,firststeps,steps,u,v)"
    and ok: "check_lp_affine_loop_xml xml"
  shows "\<exists>ts :: ((string,nat list) lab,string) term list.
    length ts=arity \<and> (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
  by (rule lp_finite_affine_loop_check_sound)
    (use parsed ok in \<open>simp add: check_lp_affine_loop_xml_def\<close>)

theorem lp_recurrent_pair_category_no:
  assumes parsed: "parse_xml_string lp_recurrent_pair_parser xml =
    Right (logic_to_program P,(q,length modes,positions),A,C,x,y,s,d,n,m,a,b,c,keep,steps1,steps2)"
    and accepted: "check_lp_recurrent_pair_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
  by (rule lp_checked_finite_witness_no[OF modes])
    (use check_lp_recurrent_pair_xml_finite_sound[OF parsed accepted] in auto)

theorem lp_pattern_loop_category_no:
  assumes parsed: "parse_xml_string lp_pattern_loop_parser xml =
    Right (logic_to_program P,(q,length modes,positions),A,sig,mu,firststeps,steps,acc)"
    and accepted: "check_lp_pattern_loop_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
  by (rule lp_checked_finite_witness_no[OF modes])
    (use check_lp_pattern_loop_xml_finite_sound[OF parsed accepted] in auto)

theorem lp_affine_loop_category_no:
  assumes parsed: "parse_xml_string lp_affine_loop_parser xml =
    Right (logic_to_program P,(q,length modes,positions),c,z,env,A,firststeps,steps,u,v)"
    and accepted: "check_lp_affine_loop_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "\<not>lp_finite_terminates P q modes \<and> \<not>lp_rational_terminates P q modes \<and>
    \<not>lp_infinite_terminates P q modes"
  by (rule lp_checked_finite_witness_no[OF modes])
    (use check_lp_affine_loop_xml_finite_sound[OF parsed accepted] in auto)
ML \<open>
  val results = @{thms lp_source_loop_category_no lp_source_trace_category_no lp_source_unify_category_no lp_source_neutral_category_no lp_recurrent_pair_category_no lp_pattern_loop_category_no lp_affine_loop_category_no}
  val _ = if Thm_Deps.has_skip_proof results then error "Pure LP NO dispatcher: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val _ = if null names then () else error ("Pure LP NO dispatcher: oracle dependency: " ^ commas names)
  val _ = warning "Pure LP NO dispatcher: all seven endpoints, including pattern acceleration; no oracle dependencies: none"
\<close>

end
