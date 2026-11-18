theory LP_Prolog_Observer_Block_Contract
 imports LP_Prolog_Observer_Protection_Control
begin

text \<open>A local block can retain evidence acquired by its first actual
step until its second actual step. The intermediate predicate is not assumed
at arbitrary graph entries. Every first and second outcome must be covered;
the checked residual descent and final caller invariant remain mandatory.\<close>

lemma lpp_observer_two_step_contract:
 assumes first: "\<And>event result.
   lpp_domain_answers P B U D (lpc_attach_answers rest (lpc_reinterface observe runtime)) event result \<Longrightarrow>
   event=None \<and> (\<exists>middle. result=lpc_attach_answers rest (lpc_reinterface observe middle) \<and> acquired middle)"
 and second: "\<And>middle event result. acquired middle \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers rest (lpc_reinterface observe middle)) event result \<Longrightarrow>
   event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface observe child) \<and>
     (subject,u)\<in>R\<^sup>+ \<and> represented child u \<and> J child)"
 and lower: "\<And>child u. (subject,u)\<in>R\<^sup>+ \<Longrightarrow> represented child u \<Longrightarrow> J child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface observe child)) R u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface observe runtime)) R subject returned"
proof (rule lp_answer_contract_intro)
 fix event result
 assume step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface observe runtime)) event result"
 obtain middle where silent: "event=None"
 and exact: "result=lpc_attach_answers rest (lpc_reinterface observe middle)"
 and evidence: "acquired middle"
  using first[OF step] by blast
 have contract: "lp_answer_contract (lpp_domain_answers P B U D) result R subject returned"
  unfolding exact by (rule lpp_observer_silent_contract[OF second[OF evidence] lower])
 show "(\<forall>rho. event=Some rho \<longrightarrow> (subject,returned rho)\<in>R\<^sup>*) \<and>
   lp_answer_contract (lpp_domain_answers P B U D) result R subject returned"
  using silent contract by simp
qed

ML \<open>
val checked = @{thms lpp_observer_two_step_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer block contract" else ();
\<close>
end
