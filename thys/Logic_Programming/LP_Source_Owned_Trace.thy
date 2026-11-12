theory LP_Source_Owned_Trace
 imports LP_Source_Owned_Pending
begin

text \<open>A finite nonempty source trace can retain an arbitrary saved caller
stack. Every executed cut must own its barrier, and every successor must remain
nonempty and have scopes disjoint from that caller. In particular an uncaught
error is not a recurring trace.\<close>

definition lpp_owned_trace_relation where
 "lpp_owned_trace_relation P U bs = {(s,t). (s,t)\<in>lpp_builtin_source P U \<and>
   t\<noteq>[] \<and> lpc_no_owned_suffix s \<and>
   (\<Union>e\<in>set t. lp_cut_entry_scopes e) \<inter>
   (\<Union>e\<in>set bs. lp_cut_entry_scopes e) = {}}"

lemma lpp_owned_trace_pending:
 assumes trace: "(s,t)\<in>(lpp_owned_trace_relation P U bs)\<^sup>+"
 shows "(s@bs,t@bs)\<in>(lpp_builtin_source P U)\<^sup>+"
 using trace
proof (induct rule: trancl_induct)
 case (base t)
 have step: "(s@bs,t@bs)\<in>lpp_builtin_source P U"
   using base by (auto simp: lpp_owned_trace_relation_def intro: lpp_builtin_owned_source_pending)
 show ?case by (rule r_into_trancl[OF step])
next
 case (step y z)
 have last: "(y@bs,z@bs)\<in>lpp_builtin_source P U"
   using step.hyps(2) by (auto simp: lpp_owned_trace_relation_def intro: lpp_builtin_owned_source_pending)
 show ?case using step last by (meson trancl_into_trancl)
qed

ML \<open>
val checked = [@{thm lpp_owned_trace_pending}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted owned source trace dependency" else ();
\<close>
end
