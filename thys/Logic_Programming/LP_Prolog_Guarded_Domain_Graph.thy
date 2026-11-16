theory LP_Prolog_Guarded_Domain_Graph
 imports LP_Prolog_Domain_Choice LP_Prolog_Domain_Cut_Module
begin

datatype lpp_guarded_domain_module = LPPGuardedPlain lpp_domain_module |
 LPPGuardedChoice lpp_scalar_guard lpp_scalar_guard lpp_domain_module lpp_domain_module |
 LPPGuardedCut "lpp_domain_prefix list list" lpp_domain_module
fun lpp_guarded_module_interface where
 "lpp_guarded_module_interface (LPPGuardedCut segments m)=m"
|
 "lpp_guarded_module_interface (LPPGuardedPlain m)=m"
| "lpp_guarded_module_interface (LPPGuardedChoice g h a b)=a"
definition lpp_guarded_module_q where
 "lpp_guarded_module_q m=lpp_domain_module_q (lpp_guarded_module_interface m)"
definition lpp_guarded_module_observations where
 "lpp_guarded_module_observations m=lpp_domain_module_observations (lpp_guarded_module_interface m)"
fun lpp_guarded_module_check where
 "lpp_guarded_module_check P modules (LPPGuardedCut segments m)=
   lpp_domain_cut_module_check P (map lpp_guarded_module_interface modules) segments m"
|
 "lpp_guarded_module_check P modules (LPPGuardedPlain m)=
   lpp_domain_module_check P (map lpp_guarded_module_interface modules) m"
| "lpp_guarded_module_check P modules (LPPGuardedChoice g h a b)=
   lpp_domain_choice_check P (map (\<lambda>m. (lpp_guarded_module_q m,lpp_guarded_module_observations m)) modules) g h a b"
definition lpp_guarded_domain_graph_check where
 "lpp_guarded_domain_graph_check P modules = list_all (lpp_guarded_module_check P modules) modules"

lemma lpp_guarded_module_progress:
 assumes checked: "lpp_guarded_module_check P modules m"
 and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
    (lpp_guarded_module_observations m) actuals"
 shows "\<exists>j next_args pending saved. j<length modules \<and>
   lpp_domain_observations (lpp_binary64_profile_operation fallback)
      (lpp_guarded_module_observations (modules!j)) next_args \<and>
   (LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q m)) actuals)#gs)#es,
    LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q (modules!j))) next_args)#pending)#saved)\<in>
      (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof (cases m)
 case (LPPGuardedPlain a)
 have ok: "lpp_domain_module_check P (map lpp_guarded_module_interface modules) a"
   using checked by (simp add: LPPGuardedPlain)
 have obs: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
   (lpp_domain_module_observations a) actuals"
   using observed by (simp add: LPPGuardedPlain lpp_guarded_module_observations_def)
 show ?thesis using lpp_domain_module_progress[OF ok obs, where gs=gs and es=es]
   by (auto simp: LPPGuardedPlain lpp_guarded_module_q_def lpp_guarded_module_observations_def; blast)
next
 case (LPPGuardedChoice g h a b)
 have ok: "lpp_domain_choice_check P (map (\<lambda>m. (lpp_guarded_module_q m,lpp_guarded_module_observations m)) modules) g h a b"
   using checked by (simp add: LPPGuardedChoice)
 have obs: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
   (lpp_domain_module_observations a) actuals"
   using observed by (simp add: LPPGuardedChoice lpp_guarded_module_observations_def)
 show ?thesis using lpp_domain_choice_progress[OF ok obs, where gs=gs and es=es]
   by (auto simp: LPPGuardedChoice lpp_guarded_module_q_def lpp_guarded_module_observations_def; blast)
next
 case (LPPGuardedCut segments a)
 have ok: "lpp_domain_cut_module_check P (map lpp_guarded_module_interface modules) segments a"
   using checked by (simp add: LPPGuardedCut)
 have obs: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
   (lpp_domain_module_observations a) actuals"
   using observed by (simp add: LPPGuardedCut lpp_guarded_module_observations_def)
 show ?thesis using lpp_domain_cut_module_progress[OF ok obs, where gs=gs and es=es]
   by (auto simp: LPPGuardedCut lpp_guarded_module_q_def lpp_guarded_module_observations_def; blast)
qed

lemma lpp_guarded_domain_graph_nontermination:
 assumes checked: "lpp_guarded_domain_graph_check P modules" and bound: "i<length modules"
 and observed: "lpp_domain_observations (lpp_binary64_profile_operation fallback)
    (lpp_guarded_module_observations (modules!i)) actuals"
 shows "\<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
   {LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q (modules!i))) actuals)#gs)#es}"
proof -
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?states = "{s. \<exists>j args pending saved. j<length modules \<and>
    s=LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q (modules!j))) args)#pending)#saved \<and>
    lpp_domain_observations ?operation (lpp_guarded_module_observations (modules!j)) args}"
 have start: "LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q (modules!i))) actuals)#gs)#es\<in>?states"
   using bound observed by blast
 have successors: "\<exists>v\<in>?states. (s,v)\<in>?R\<^sup>+" if member: "s\<in>?states" for s
 proof -
  obtain j args pending saved where j: "j<length modules" and shape:
   "s=LPCGoals (LPCAtom (LPIFun (LPCUser (lpp_guarded_module_q (modules!j))) args)#pending)#saved"
   and obs: "lpp_domain_observations ?operation (lpp_guarded_module_observations (modules!j)) args"
   using member by blast
  have node: "lpp_guarded_module_check P modules (modules!j)"
    using checked j by (simp add: lpp_guarded_domain_graph_check_def list_all_iff)
  show ?thesis using lpp_guarded_module_progress[OF node obs, where gs=pending and es=saved] shape by blast
 qed
 show ?thesis
   by (rule lp_source_recurrent_simulation[where X="{()}" and a="()" and S="{((),())}"
      and rep="\<lambda>_ s. s\<in>?states"])
     (use start successors in auto)
qed

ML \<open>
val checked = [@{thm lpp_guarded_domain_graph_nontermination}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted domain recurrence graph dependency" else ();
\<close>
end
