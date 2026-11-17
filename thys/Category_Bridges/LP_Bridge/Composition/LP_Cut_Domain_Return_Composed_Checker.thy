theory LP_Cut_Domain_Return_Composed_Checker
  imports LP_Cut_Domain_Return_Composed_Certificate
begin

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem domain_return_composed_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,(R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_return_composed_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule precise_return_composed_constructor_sound[OF domain tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_composed_constructor_xml_def\<close>)
end

context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)

theorem ranked_return_composed_xml_yes:
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (cut_program P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and accepted: "check_lpc_return_composed_constructor_xml xml"
    and program: "cut_control_program P"
    and erasure: "cut_mgu_erasure D"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program P) (q,length modes) modes"
apply (rule precise_native_termination[OF program erasure])
  subgoal by (rule projection; assumption)
  subgoal by (rule domain_return_composed_xml_sound[OF domain parsed accepted]; assumption)
  done
end

text \<open>The guarded boundary checks ordinary heads and control arities.
Its acceptance is stronger than acceptance by the unchanged native checker.\<close>
definition check_lpc_ranked_return_composed_xml :: "string \<Rightarrow> bool" where
  "check_lpc_ranked_return_composed_xml xml \<longleftrightarrow> check_lpc_return_composed_constructor_xml xml \<and>
    (case parse_xml_string lpc_return_composed_constructor_parser xml of
      Left e \<Rightarrow> False |
      Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf)) \<Rightarrow>
        cut_program_shape P \<and> cut_control_program (cut_program_back P))"

lemma ranked_return_composed_guarded_yes:
  assumes domain: "cut_runtime_domain D"
    and parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_return_composed_xml xml"
    and erasure: "cut_mgu_erasure D"
    and projection: "\<And>u. D (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      D (cut_tree (cut_unrank_tree (logic_arity_project (logic_symbol_arity snd) undefined u)))"
  shows "logic_cut_terminates_in snd (\<lambda>t. D (cut_tree (cut_unrank_tree t)))
    (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have shape: "cut_program_shape P" and control: "cut_control_program (cut_program_back P)"
    and accepted: "check_lpc_return_composed_constructor_xml xml"
    using checked parsed by (auto simp: check_lpc_ranked_return_composed_xml_def)
  have inverse: "cut_program (cut_program_back P) = P"
    by (rule cut_program_forward_back[OF shape])
  show ?thesis by (rule ranked_return_composed_xml_yes[OF domain _ accepted control erasure projection])
    (simp only: inverse parsed)
qed
corollary lp_cut_return_composed_finite_yes:
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_return_composed_xml xml"
  shows "lp_cut_finite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have projection: "cut_finite_runtime (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      cut_finite_runtime (cut_tree (cut_unrank_tree
        (logic_arity_project (logic_symbol_arity snd) undefined u)))" for u
    by (simp add: cut_finite_domain_iff cut_finite_projection_closed)
  have domains: "(\<lambda>t. cut_finite_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_finite t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_finite_domain_iff cut_typed_unrank_finite)
  show ?thesis using ranked_return_composed_guarded_yes[OF finite_cut.cut_runtime_domain_axioms parsed checked cut_finite_mgu_erasure projection]
    by (simp add: lp_cut_finite_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_return_composed_rational_yes:
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_return_composed_xml xml"
  shows "lp_cut_rational_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
proof -
  have projection: "cut_rational_runtime (cut_tree (cut_unrank_tree u)) \<Longrightarrow>
      cut_rank_tree (cut_unrank_tree u) = u \<Longrightarrow>
      cut_rational_runtime (cut_tree (cut_unrank_tree
        (logic_arity_project (logic_symbol_arity snd) undefined u)))" for u
    by (simp add: cut_rational_runtime_def cut_rational_projection_closed)
  have domains: "(\<lambda>t. cut_rational_runtime (cut_tree (cut_unrank_tree t)) \<and>
      logic_tree_arity_correct (logic_symbol_arity snd) t) =
    (\<lambda>t. logic_rational t \<and> logic_tree_arity_correct (logic_symbol_arity snd) t)"
    by (rule ext) (auto simp: cut_rational_runtime_def cut_typed_unrank_rational)
  show ?thesis using ranked_return_composed_guarded_yes[OF rational_cut.cut_runtime_domain_axioms parsed checked cut_rational_mgu_erasure projection]
    by (simp add: lp_cut_rational_terminates_def logic_cut_termination_domain_cong[OF domains])
qed

corollary lp_cut_return_composed_infinite_yes:
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and checked: "check_lpc_ranked_return_composed_xml xml"
  shows "lp_cut_infinite_terminates snd (cut_rank_program (cut_program_back P)) (q,length modes) modes"
  using ranked_return_composed_guarded_yes[OF cut_unrestricted_runtime parsed checked cut_infinite_mgu_erasure]
  by (simp add: lp_cut_infinite_terminates_def)


ML \<open>
  val results = @{thms lp_cut_return_composed_finite_yes lp_cut_return_composed_rational_yes lp_cut_return_composed_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked return_composed checker: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Ranked return_composed checker: unexpected oracles: " ^ commas unexpected)
\<close>
end
