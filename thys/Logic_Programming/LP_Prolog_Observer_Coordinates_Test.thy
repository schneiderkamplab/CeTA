theory LP_Prolog_Observer_Coordinates_Test
 imports LP_Prolog_Observer_Coordinates
begin
lemma coordinate_rebase_copy:
 "lpc_check_coordinate_transport [(Inl (2::nat),Inr (1::nat))]
   [(Inl (0::nat),Inr (1::nat))] (case_sum (\<lambda>_. Inl 2) Inr)"
 by (simp add: lpc_check_coordinate_transport_def)
lemma coordinate_missing_relation_rejected:
 "\<not>lpc_check_coordinate_transport ([]::((nat+nat)*(nat+nat)) list)
   [(Inl (0::nat),Inr (1::nat))] (case_sum (\<lambda>_. Inl 2) Inr)"
 by (simp add: lpc_check_coordinate_transport_def)
lemma coordinate_wrong_route_rejected:
 "\<not>lpc_check_coordinate_transport [(Inl (2::nat),Inr (1::nat))]
   [(Inl (0::nat),Inr (1::nat))] (case_sum (\<lambda>_. Inl 0) Inr)"
 by (simp add: lpc_check_coordinate_transport_def)
lemma coordinate_initialization_bounds:
 "\<not>lpc_check_coordinate_initialization [(0,1)] [value]"
 by (simp add: lpc_check_coordinate_initialization_def)
lemma coordinate_initialization_distinct:
 "left\<noteq>right \<Longrightarrow> \<not>lpc_check_coordinate_initialization [(0,1)] [left,right]"
 by (simp add: lpc_check_coordinate_initialization_def)
end
