theory LP_Prolog_Domain_Cut_Module
 imports LP_Prolog_Domain_Cut_Edge LP_Prolog_Domain_Graph
begin
fun lpp_domain_cut_module_check where
 "lpp_domain_cut_module_check P modules segments (LPPDomainModule q obs sel H actions outputs recipes failures dest) =
  (dest<length modules \<and>
   lpp_domain_cut_edge_check P q obs sel H segments actions outputs recipes failures
     (lpp_domain_module_q (modules!dest)) (lpp_domain_module_observations (modules!dest)))"
lemma lpp_domain_cut_module_progress:
 assumes checked: "lpp_domain_cut_module_check P modules segments m"
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
  "lpp_domain_cut_edge_check P q obs sel H segments actions outputs recipes failures
     (lpp_domain_module_q (modules!dest)) (lpp_domain_module_observations (modules!dest))"
  using checked by (simp_all add: LPPDomainModule)
 have observed': "lpp_domain_observations (lpp_binary64_profile_operation fallback) obs actuals"
  using observed by (simp add: LPPDomainModule)
 show ?thesis using lpp_domain_cut_edge_progress[OF edge observed', where gs=gs and es=es] bound
  by (auto simp: LPPDomainModule)
qed


end
