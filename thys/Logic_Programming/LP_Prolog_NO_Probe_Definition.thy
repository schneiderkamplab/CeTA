theory LP_Prolog_NO_Probe_Definition
 imports LP_Prolog_Probe_Builtin
begin

definition lpp_no_return_probe where
 "lpp_no_return_probe m n ss tt = (case ss of
   (LPCGoals (LPCAtom (Fun (LPCUser f) [Fun (LPCUser g) argv])#gs),payload)#saved \<Rightarrow>
   (lpp_probe_name f \<and> lp_cut_fresh m (LPCGoals gs#map fst saved) \<and>
    lp_cut_fresh n (LPCBarrier m#LPCGoals gs#map fst saved) \<and>
    tt=lpp_probe_stack (Fun (LPCUser g) argv) (f=''1:once'') m n gs payload saved)
 | _ \<Rightarrow> False)"

definition lpp_no_plain_probe :: "nat \<Rightarrow> nat \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_entry list \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_entry list \<Rightarrow> bool" where
 "lpp_no_plain_probe m n ss tt =
   lpp_no_return_probe m n (map (\<lambda>e. (e,[] :: (string lp_cut_symbol,string) term list)) ss)
     (map (\<lambda>e. (e,[] :: (string lp_cut_symbol,string) term list)) tt)"

end
