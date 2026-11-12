theory LP_Prolog_NO_List_Definition
 imports LP_Prolog_List_Observation
begin

fun lpp_no_return_list where
 "lpp_no_return_list fuel held
   ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),payload)#saved) tt =
  (f=''1:is_list'' \<and> lpp_check_list_observation fuel a=Some held \<and>
   tt=(if held then (LPCGoals gs,payload)#saved else saved))"
| "lpp_no_return_list fuel held ss tt = False"

definition lpp_no_plain_list :: "nat \<Rightarrow> bool \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_entry list \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_entry list \<Rightarrow> bool" where
 "lpp_no_plain_list fuel held ss tt = lpp_no_return_list fuel held
   (map (\<lambda>e. (e,[] :: (string lp_cut_symbol,string) term list)) ss)
   (map (\<lambda>e. (e,[] :: (string lp_cut_symbol,string) term list)) tt)"

end
