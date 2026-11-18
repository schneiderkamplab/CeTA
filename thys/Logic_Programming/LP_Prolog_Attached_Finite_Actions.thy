theory LP_Prolog_Attached_Finite_Actions
 imports LP_Prolog_Functor_Reflexive_Contract LP_Prolog_Separation_Univ_Transport
begin

text \<open>Finite local execution does not by itself cover suspended caller
terms. Expose the per-choice-frame continuation obligation and apply the existing
finite-step rules to the actual attached state, with its original environments.\<close>

lemma lpp_finite_goals_append:
 "lpp_finite_goals (xs@ys) = (lpp_finite_goals xs \<and> lpp_finite_goals ys)"
 by (simp add: lpp_finite_goals_def)

lemma lpp_finite_attached_frame:
 "lpp_finite_execution_entry (lpc_attach_frame rest (source_frame,eta)) =
   (lpp_finite_execution_entry source_frame \<and>
    (case source_frame of LPCBarrier m \<Rightarrow> True | _ \<Rightarrow>
       lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) rest)))"
 by (cases source_frame) (simp_all add: lpp_finite_goals_append)

lemma lpp_finite_attached_execution:
 "lpp_finite_execution (lpc_attach_answers rest ss) =
   (lpp_finite_execution ss \<and> list_all (\<lambda>frame.
    case fst frame of LPCBarrier m \<Rightarrow> True | _ \<Rightarrow>
     lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t (snd frame))) rest)) ss)"
 by (induct ss) (auto simp: lpp_finite_execution_def lpc_attach_answers_def
   lpp_finite_goals_append split: prod.splits lp_cut_entry.splits)

lemma lpp_finite_attached_matching_step:
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#gs) c m,ret)#saved))"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 shows "lpp_finite_execution tt"
 using lpp_finite_matching_resolution_base_step[OF _ _ matching] step finite
 by (simp add: lpc_attach_answers_def)

lemma lpp_finite_attached_ground_equality_step:
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved))"
 and ground: "lp_seg_ground b"
 shows "lpp_finite_execution tt"
 using lpp_finite_ground_equality_base_step[OF _ _ ground] step finite
 by (simp add: lpc_attach_answers_def)

lemma lpp_finite_attached_reflexive_step:
 assumes step: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved)) event tt"
 and finite: "lpp_finite_execution
   (lpc_attach_answers rest ((LPCGoals (LPCUnify a b#gs),eta)#saved))"
 and equal: "a=b"
 shows "lpp_finite_execution tt"
 using lpp_finite_reflexive_equality_base_step[OF _ _ equal] step finite
 by (simp add: lpc_attach_answers_def)

lemma lpp_finite_attached_pair_step:
 assumes step: "lpc_answer_transition P (lpc_attach_answers rest
   ((LPCGoals (LPCUnify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b])#gs),eta)#saved)) event tt"
 and finite: "lpp_finite_execution (lpc_attach_answers rest
   ((LPCGoals (LPCUnify (LPIFun f [LPIVar x,LPIVar y]) (LPIFun f [a,b])#gs),eta)#saved))"
 and distinct: "x\<noteq>y"
 and fresh: "{x,y}\<inter>(set2_lp_iterm a\<union>set2_lp_iterm b)={}"
 shows "lpp_finite_execution tt"
 using lpp_finite_separated_pair_base_step[OF _ _ distinct fresh] step finite
 by (simp add: lpc_attach_answers_def)

lemma lpp_finite_prefix_does_not_cover_suspended_value:
 assumes nonfinite: "\<not>lpp_finite_term (eta x)"
 shows "lpp_finite_execution [(LPCGoals [],eta)] \<and>
   \<not>lpp_finite_execution (lpc_attach_answers [LPCAtom (Var x)] [(LPCGoals [],eta)])"
 using nonfinite by (simp add: lpp_finite_execution_def lpc_attach_answers_def lpp_finite_goals_def)


lemma lpp_simple_active_attachment:
 assumes simple: "lpp_simple_control_frame ss" and active: "lpc_prefix_active ss"
 shows "lpp_simple_control_frame (lpc_attach_answers rest ss)"
proof (cases ss)
 case Nil then show ?thesis using active by simp
next
 case (Cons frame tail)
 obtain source_frame rho where frame: "frame=(source_frame,rho)" by (cases frame) auto
 show ?thesis
 proof (cases source_frame)
  case (LPCGoals gs)
  show ?thesis
  proof (cases gs)
   case Nil then show ?thesis using active by (simp add: Cons frame LPCGoals)
  next
   case (Cons g more)
   show ?thesis using simple active
    by (cases g) (simp_all add: \<open>ss=frame#tail\<close> frame LPCGoals Cons lpc_attach_answers_def)
  qed
 qed (use simple in \<open>simp_all add: Cons frame lpc_attach_answers_def\<close>)
qed

lemma lpp_finite_attached_simple_step:
 assumes simple: "lpp_simple_control_frame ss" and active: "lpc_prefix_active ss"
 and step: "lpc_answer_transition P (lpc_attach_answers rest ss) event tt"
 and finite: "lpp_finite_execution (lpc_attach_answers rest ss)"
 shows "lpp_finite_execution tt"
 by (rule lpp_finite_simple_base_step[OF lpp_simple_active_attachment[OF simple active] step finite])

lemma lpp_saved_suspended_environment_required:
 assumes bad: "\<not>lpp_finite_term (saved_env x)"
 shows "\<not>lpp_finite_execution (lpc_attach_answers [LPCAtom (Var x)]
   [(LPCGoals gs,active_env),(LPCGoals [],saved_env)])"
 using bad by (simp add: lpp_finite_execution_def lpc_attach_answers_def lpp_finite_goals_def)

ML \<open>
val checked = @{thms lpp_finite_goals_append lpp_finite_attached_frame
 lpp_finite_attached_execution lpp_finite_attached_matching_step
 lpp_finite_attached_ground_equality_step lpp_finite_attached_reflexive_step
 lpp_finite_attached_pair_step lpp_finite_prefix_does_not_cover_suspended_value
 lpp_simple_active_attachment lpp_finite_attached_simple_step lpp_saved_suspended_environment_required};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached finite action" else ();
\<close>
end
