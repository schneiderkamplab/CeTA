theory LP_Source_Call_Recurrence
 imports LP_Cut_NO_Return_Attachment
begin

text \<open>A recurring family retains arbitrary finite delayed goals and saved
alternatives. Reaching another selected call is useful only when a nonempty
source path can be repeated from every member of this family. The criterion is
shared by source relations with checked builtin extensions.\<close>

theorem lp_source_call_recurrence:
 fixes R :: "('f,string) lp_iterm lp_cut_entry list rel"
   and A :: "('f,string) term set"
 assumes initial: "a \<in> A"
   and repeat: "\<And>b gs es. b \<in> A \<Longrightarrow> \<exists>c\<in>A. \<exists>hs fs.
     (lp_cut_state_eval (LPCGoals (LPCAtom b#gs)#es) LPIVar,
      lp_cut_state_eval (LPCGoals (LPCAtom c#hs)#fs) LPIVar) \<in> R\<^sup>+"
 shows "\<not> SN_on R {lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar}"
proof -
 let ?X = "{lp_cut_state_eval (LPCGoals (LPCAtom b#gs)#es) LPIVar |b gs es. b\<in>A}"
 have member: "lp_cut_state_eval (LPCGoals (LPCAtom a#rest)#saved) LPIVar \<in> ?X"
   using initial by blast
 have successor: "\<forall>u\<in>?X. \<exists>v\<in>?X. (u,v)\<in>R\<^sup>+"
   using repeat by blast
 show ?thesis using lower_set_imp_not_SN_on[OF member successor] SN_on_trancl by blast
qed

ML \<open>
val checked = [@{thm lp_source_call_recurrence}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted call recurrence dependency" else ();
\<close>
end
