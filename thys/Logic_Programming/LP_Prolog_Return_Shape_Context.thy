theory LP_Prolog_Return_Shape_Context
  imports LP_Prolog_Return_Shapes LP_Prolog_Evaluation_Context
begin

text \<open>Use only successful-helper facts already justified in the current
source context. Failure alternatives require their own context proof; this
lemma introduces no history-based assumptions or termination claims.\<close>

lemma lpp_return_shape_context_flow:
  fixes P :: "'v lpp_success_clause list"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm"
  assumes checked: "lp_return_shape_program_check fuel G modes (lpp_shape_program P)"
    and observed: "lpp_evaluation_context_holds E P (facts,guards,observations) eta"
    and known: "lp_return_shape_known G seed_facts eta"
  shows "lp_return_facts_valid G eta
    (lp_return_shape_flow fuel G modes (map lpp_lift_atom facts) (Some seed_facts))"
proof -
  have lift: "lpp_lift_iatom (lpp_success_atom_eval b eta)=lp_atom_eval (lpp_lift_atom b) eta" for b
    by (cases b) (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lpp_lift_atom_def lp_atom_eval_def)
  have body: "\<forall>b\<in>set (map lpp_lift_atom facts). lp_return_contracts G modes (lp_atom_eval b eta)"
  proof -
    have "lp_return_contracts G modes (lp_atom_eval (lpp_lift_atom b) eta)"
      if "b\<in>set facts" for b
      using lpp_guarded_return_shape_contracts[OF checked, of E "lpp_success_atom_eval b eta"]
        observed that
      by (auto simp: lpp_evaluation_context_holds_def list_all_iff lift)
    then show ?thesis by auto
  qed
  show ?thesis by (rule lp_return_shape_flow_sound[OF body])
    (use known in \<open>simp add: lp_return_facts_valid_def\<close>)
qed

lemma lpp_return_shape_context_ground:
  fixes P :: "'v lpp_success_clause list"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm"
  assumes checked: "lp_return_shape_program_check fuel G modes (lpp_shape_program P)"
    and observed: "lpp_evaluation_context_holds E P (facts,guards,observations) eta"
    and known: "lp_return_shape_known G seed_facts eta"
    and flow: "lp_return_shape_flow fuel G modes (map lpp_lift_atom facts) (Some seed_facts)=Some result"
    and member: "(LPReturnGround,x)\<in>set result"
  shows "lp_seg_ground (eta x)"
  using lpp_return_shape_context_flow[OF checked observed known] flow member
  by (auto simp: lp_return_facts_valid_def lp_return_shape_known_def lp_return_ground_exact)


definition lpp_return_shape_context_ground_vars where
  "lpp_return_shape_context_ground_vars fuel G modes facts seeds =
    (case lp_return_shape_flow fuel G modes (map lpp_lift_atom facts)
       (Some (map (Pair LPReturnGround) seeds)) of None \<Rightarrow> []
     | Some result \<Rightarrow> map snd (filter (\<lambda>(s,x). s=LPReturnGround) result))"

lemma lpp_return_shape_context_ground_vars_sound:
  fixes P :: "'v lpp_success_clause list"
    and eta :: "'v \<Rightarrow> (string lp_cut_symbol,'v) lp_iterm"
  assumes checked: "lp_return_shape_program_check fuel G modes (lpp_shape_program P)"
    and observed: "lpp_evaluation_context_holds E P (facts,guards,observations) eta"
    and seeds: "\<forall>x\<in>set seeds. lp_seg_ground (eta x)"
  shows "\<forall>x\<in>set (lpp_return_shape_context_ground_vars fuel G modes facts seeds).
    lp_seg_ground (eta x)"
proof -
  have known: "lp_return_shape_known G (map (Pair LPReturnGround) seeds) eta"
    using seeds by (auto simp: lp_return_shape_known_def lp_return_ground_exact)
  have valid: "lp_return_facts_valid G eta
    (lp_return_shape_flow fuel G modes (map lpp_lift_atom facts)
      (Some (map (Pair LPReturnGround) seeds)))"
    by (rule lpp_return_shape_context_flow[OF checked observed known])
  show ?thesis using valid
    by (auto simp: lpp_return_shape_context_ground_vars_def lp_return_facts_valid_def
      lp_return_shape_known_def lp_return_ground_exact split: option.splits)
qed

ML \<open>
val audited = [@{thm lpp_return_shape_context_flow}, @{thm lpp_return_shape_context_ground},
  @{thm lpp_return_shape_context_ground_vars_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted Prolog return-shape context dependency" else ();
\<close>

end
