theory LP_Prolog_Return_Shape_Control
  imports LP_Prolog_Return_Shape_Context LP_Prolog_Evaluation_Control LP_Prolog_Evaluation_Transport
begin

definition lpp_shape_local_context where
  "lpp_shape_local_context shape_fuel G modes seeds context =
    lpp_context_add_ground context
      (lpp_return_shape_context_ground_vars shape_fuel G modes (fst context) seeds)"

lemma lpp_shape_local_context_sound:
  fixes SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP)"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP context eta"
    and seeds: "\<forall>x\<in>set seeds. lp_seg_ground (eta x)"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result SP
    (lpp_shape_local_context shape_fuel G modes seeds context) eta"
proof -
  obtain facts guards observations where ctx: "context=(facts,guards,observations)"
    by (cases "context") auto
  have ground: "\<forall>x\<in>set (lpp_return_shape_context_ground_vars shape_fuel G modes facts seeds).
    lp_seg_ground (eta x)"
    by (rule lpp_return_shape_context_ground_vars_sound[OF checked _ seeds])
      (use observed ctx in simp)
  show ?thesis unfolding lpp_shape_local_context_def ctx
    by (rule lpp_evaluation_add_ground_sound)
      (use observed ctx ground in auto)
qed

definition lpp_shape_local_contexts where
  "lpp_shape_local_contexts shape_fuel G modes seedss contexts =
    map (\<lambda>i. lpp_shape_local_context shape_fuel G modes (seedss!i) (contexts!i)) [0..<length contexts]"

definition lpp_check_shape_evaluation_control where
  "lpp_check_shape_evaluation_control shape_fuel G modes seedss SP fuel P Q nds states contexts Fs T returned arity actions =
    (lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP) \<and>
     length seedss=length nds \<and>
     list_all (\<lambda>i. set (seedss!i) \<subseteq> set (lpcn_ground (nds!i)) \<union>
       lpp_source_context_ground (contexts!i)) [0..<length nds] \<and>
     lpp_check_evaluation_control_contexts fuel P Q nds states contexts
       (lpp_shape_local_contexts shape_fuel G modes seedss contexts) Fs T returned arity actions)"

lemma lpp_check_shape_evaluation_control_enrich:
  fixes SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_check_shape_evaluation_control shape_fuel G modes seedss SP fuel P Q nds states contexts Fs T returned arity actions"
    and index: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!i) eta"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result SP
    (lpp_shape_local_contexts shape_fuel G modes seedss contexts!i) eta"
proof -
  have bound: "i<length contexts"
    and model: "lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP)"
    and subset: "set (seedss!i) \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
    using checked index by (auto simp: lpp_check_shape_evaluation_control_def
      lpp_check_evaluation_control_contexts_def list_all_iff)
  have seeds: "\<forall>x\<in>set (seedss!i). lp_seg_ground (eta x)"
    using subset known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
    by (auto simp: lp_cut_knowledge_def)
  show ?thesis using lpp_shape_local_context_sound[OF model observed seeds] bound
    by (simp add: lpp_shape_local_contexts_def)
qed

end
