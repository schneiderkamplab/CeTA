theory LP_Prolog_Observer_Finite_Helper
 imports LP_Prolog_Observer_Fresh_Univ_Assembled
begin

lemma lpp_observer_finite_reinterface:
 "lpp_finite_execution (lpc_reinterface F ss)=lpp_finite_execution ss"
 by (auto simp: lpp_finite_execution_def lpc_reinterface_def list_all_iff split: prod.splits)

lemma lpp_observer_finite_detach:
 assumes "lpp_finite_execution (lpc_attach_answers rest ss)"
 shows "lpp_finite_execution ss"
proof -
 have frame: "lpp_finite_execution_entry (fst row)" if
  "lpp_finite_execution_entry (lpc_attach_frame rest row)" for row
  using that by (cases row; case_tac a) (auto simp: lpp_finite_goals_def)
 show ?thesis using assms frame
  by (auto simp: lpp_finite_execution_def lpc_attach_answers_def list_all_iff)
qed

lemma lpp_observer_invariant_finite_helper:
 assumes "lpp_observer_invariant A specs rest runtime"
 shows "lpp_finite_execution (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime)"
proof -
 have attached: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))"
  using assms by (simp add: lpp_observer_invariant_def)
 have finite: "lpp_finite_execution (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
  by (rule lpp_observer_finite_detach[OF attached])
 show ?thesis using finite by (simp add: lpp_observer_finite_reinterface)
qed

ML \<open>
val checked = @{thms lpp_observer_finite_reinterface lpp_observer_finite_detach lpp_observer_invariant_finite_helper};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted finite helper projection" else ();
\<close>
end
