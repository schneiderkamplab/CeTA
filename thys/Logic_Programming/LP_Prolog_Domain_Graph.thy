theory LP_Prolog_Domain_Graph
 imports LP_Prolog_Domain_Edge LP_Prolog_Scalar_Domain_NO
begin

datatype lpp_domain_module = LPPDomainModule string "lpp_recurrent_scalar_domain option list"
 nat "string list" "lpp_domain_prefix list" "(string lp_cut_symbol,string) term list"
 "lpp_scalar_template option list" "lpp_head_failure list" nat
fun lpp_domain_module_q where
 "lpp_domain_module_q (LPPDomainModule q obs sel H actions outputs recipes failures dest) = q"
fun lpp_domain_module_observations where
 "lpp_domain_module_observations (LPPDomainModule q obs sel H actions outputs recipes failures dest) = obs"
fun lpp_domain_module_destination where
 "lpp_domain_module_destination (LPPDomainModule q obs sel H actions outputs recipes failures dest) = dest"
fun lpp_domain_module_check where
 "lpp_domain_module_check P modules (LPPDomainModule q obs sel H actions outputs recipes failures dest) =
  (dest<length modules \<and>
   lpp_domain_edge_check P q obs sel H actions outputs recipes failures
     (lpp_domain_module_q (modules!dest)) (lpp_domain_module_observations (modules!dest)))"
definition lpp_domain_graph_check where
 "lpp_domain_graph_check P modules = list_all (lpp_domain_module_check P modules) modules"

lemma lpp_domain_module_progress:
 assumes checked: "lpp_domain_module_check P modules m"
 and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
    (lpp_domain_module_observations m) actuals"
 shows "\<exists>j next_args pending saved. j<length modules \<and>
   lpp_domain_observations (lpp_binary64_profile_operation fallback)
      (lpp_domain_module_observations (modules!j)) next_args \<and>
   (LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q m)) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q (modules!j))) next_args)#pending)#saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof (cases m)
 case (LPPDomainModule q obs sel H actions outputs recipes failures dest)
 have bound: "dest<length modules" and edge:
  "lpp_domain_edge_check P q obs sel H actions outputs recipes failures
     (lpp_domain_module_q (modules!dest)) (lpp_domain_module_observations (modules!dest))"
  using checked by (simp_all add: LPPDomainModule)
 have observed': "lpp_domain_observations (lpp_binary64_profile_operation fallback) obs actuals"
  using observed by (simp add: LPPDomainModule)
 show ?thesis using lpp_domain_edge_progress[OF edge observed', where gs=gs and es=es] bound
  by (auto simp: LPPDomainModule)
qed

lemma lpp_domain_graph_nontermination:
 assumes checked: "lpp_domain_graph_check P modules" and bound: "i<length modules"
 and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
    (lpp_domain_module_observations (modules!i)) actuals"
 shows "\<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
   {LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q (modules!i))) actuals)#gs)#es}"
proof -
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?states = "{s. \<exists>j args pending saved. j<length modules \<and>
    s=LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q (modules!j))) args)#pending)#saved \<and>
    lpp_domain_observations ?operation (lpp_domain_module_observations (modules!j)) args}"
 have start: "LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q (modules!i))) actuals)#gs)#es\<in>?states"
   using bound observed by blast
 have successors: "\<exists>v\<in>?states. (s,v)\<in>?R\<^sup>+" if member: "s\<in>?states" for s
 proof -
  obtain j args pending saved where j: "j<length modules" and shape:
   "s=LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_domain_module_q (modules!j))) args)#pending)#saved"
   and obs: "lpp_domain_observations ?operation (lpp_domain_module_observations (modules!j)) args"
   using member by blast
  have node: "lpp_domain_module_check P modules (modules!j)"
    using checked j by (simp add: lpp_domain_graph_check_def list_all_iff)
  show ?thesis using lpp_domain_module_progress[OF node obs, where gs=pending and es=saved] shape by blast
 qed
 show ?thesis
   by (rule lp_source_recurrent_simulation[where X="{()}" and a="()" and S="{((),())}"
      and rep="\<lambda>_ s. s\<in>?states"])
     (use start successors in auto)
qed

ML \<open>
val checked = [@{thm lpp_domain_graph_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted domain recurrence graph dependency" else ();
\<close>
end
