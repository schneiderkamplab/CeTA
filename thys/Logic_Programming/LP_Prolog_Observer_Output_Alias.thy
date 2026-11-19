theory LP_Prolog_Observer_Output_Alias
 imports LP_Prolog_Restricted_Prefix_Output LP_Prolog_Actual_Returns
begin

text \<open>The shared helper/caller interface keeps an equality of actual
values. Unlike freeness, this equality survives every source substitution,
including saved alternatives and failing builtin steps. Projection must still
identify the correct coordinate; it cannot silently drop the helper output.\<close>

definition lpp_observer_output_alias where
 "lpp_observer_output_alias oi hi runtime =
   list_all (\<lambda>frame. snd frame (Inl oi) = snd frame (Inr hi)) runtime"

lemma lpp_observer_output_alias_step:
 assumes step: "lpp_domain_answers P B U D runtime event next_runtime"
 and known: "lpp_observer_output_alias oi hi runtime"
 shows "lpp_observer_output_alias oi hi next_runtime \<and>
   (\<forall>env. event = Some env \<longrightarrow> env (Inl oi) = env (Inr hi))"
 using lpp_domain_answer_substitution_property[where F="\<lambda>env. env (Inl oi) = env (Inr hi)",
   OF _ step known[unfolded lpp_observer_output_alias_def]]
 by (simp add: lpp_observer_output_alias_def)

lemma lpp_observer_output_alias_initial:
 assumes left: "oi < length helper_payload" "helper_payload ! oi = Var helper_slot"
 and right: "hi < length caller_payload" "caller_payload ! hi = Var helper_slot"
 shows "lpp_observer_output_alias oi hi
   [(goals,case_sum (lpc_return_env helper_payload eta) (lpc_return_env caller_payload eta))]"
 using assms by (simp add: lpp_observer_output_alias_def lpc_return_env_def)

lemma lpp_observer_output_alias_projection:
 assumes known: "lpp_observer_output_alias oi hi runtime"
 and selected: "project new_oi = oi"
 shows "lpp_observer_output_alias new_oi hi
   (lpc_reinterface (\<lambda>env. case_sum (\<lambda>x. env (Inl (project x))) (\<lambda>x. env (Inr x))) runtime)"
 using assms by (auto simp: lpp_observer_output_alias_def lpc_reinterface_def
   list_all_iff split: prod.splits)

lemma lpp_observer_output_alias_scopes:
 "lpp_observer_output_alias oi hi (lpc_return_scope_word swaps runtime) =
   lpp_observer_output_alias oi hi runtime"
proof -
 have scope: "lpp_observer_output_alias oi hi (lpc_return_scope r ss) =
   lpp_observer_output_alias oi hi ss" for r ss
  by (fastforce simp: lpp_observer_output_alias_def list_all_iff)
 show ?thesis
 proof (induct swaps arbitrary: runtime)
  case Nil then show ?case by simp
 next
  case (Cons pair swaps)
  obtain a b where pair: "pair = (a,b)" by (cases pair) auto
  show ?case by (simp only: pair lpc_return_scope_word.simps Cons.hyps scope)
 qed
qed

lemma lpp_observer_output_alias_mode:
 assumes shared: "lpp_observer_output_alias oi hi ((goals,env)#saved)"
 and represented: "lpc_reinterface (\<lambda>rho x. rho (Inl x)) ((goals,env)#saved) =
   lpc_return_eval eta ((source_goals,payload)#source_saved)"
 and coordinate: "oi < length payload" "payload ! oi = output_term"
 and invariant: "lpp_observer_invariant A specs rest ((goals,env)#saved)"
 and observed: "(hi,Fun (Inr ()) []) \<in> set specs"
 and ground: "\<And>u. u \<in> A \<Longrightarrow> vars_term u = {}"
 shows "lp_ieval output_term eta = env (Inr hi) \<and>
   lpp_caller_output_mode (lp_ieval output_term eta)"
proof -
 have helper_env: "(\<lambda>x. env (Inl x)) = lpc_return_env payload eta"
  using represented by (simp add: lpc_reinterface_def lpc_return_eval_def)
 have same: "lp_ieval output_term eta = env (Inr hi)"
  using fun_cong[OF helper_env, of oi] shared coordinate
  by (simp add: lpc_return_env_def lpp_observer_output_alias_def)
 have mode: "lpp_caller_output_mode (env (Inr hi))"
  by (rule lpp_observer_restricted_output_mode[where goals=goals, OF invariant observed _ ground]) simp
 show ?thesis using same mode by simp
qed

ML \<open>
val checked = @{thms lpp_observer_output_alias_step lpp_observer_output_alias_initial
 lpp_observer_output_alias_projection lpp_observer_output_alias_scopes lpp_observer_output_alias_mode};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted observer output alias" else ();
\<close>
end
