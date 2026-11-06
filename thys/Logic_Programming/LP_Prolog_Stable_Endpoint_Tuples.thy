theory LP_Prolog_Stable_Endpoint_Tuples
 imports LP_Prolog_Stable_Numeric_Valuation
begin

lemma lpp_stable_endpoint_tuple_exists:
  assumes endpoints: "list_all (\<lambda>(coordinate,t,e). lpp_check_stable_endpoint K G t e) endpoints"
    and distinct: "distinct (map fst endpoints)"
    and known: "lpp_integer_known K eta"
    and ground: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
  shows "\<exists>rho. lpp_stable_numeric_tuple operation (map fst endpoints)
    (map (lpp_stable_endpoint_mode o snd o snd) endpoints)
    (map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints) rho"
proof -
  obtain source_values where typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    using lpp_integer_known_environment[OF known] by blast
  have each: "\<exists>k. lpp_stable_coordinate_value operation
    (lpp_stable_endpoint_mode (snd (snd e))) (lp_ieval (fst (snd e)) eta) k"
    if member: "e\<in>set endpoints" for e
  proof -
    obtain coordinate t endpoint where shape: "e=(coordinate,t,endpoint)" by (cases e) auto
    have check: "lpp_check_stable_endpoint K G t endpoint"
      using endpoints member by (auto simp: shape list_all_iff)
    show ?thesis using lpp_checked_stable_endpoint[where operation=operation and eta=eta and rho=source_values, OF check typed ground]
      by (auto simp: shape)
  qed
  have all: "list_all2 (\<lambda>mode t. \<exists>k. lpp_stable_coordinate_value operation mode t k)
      (map (lpp_stable_endpoint_mode o snd o snd) endpoints)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints)"
    using each by (auto simp: list_all2_map1 list_all2_map2 list_all2_same)
  show ?thesis by (rule lpp_stable_numeric_tuple_exists[OF distinct _ all]) simp
qed

lemma lpp_stable_numeric_tuple_endpoint:
  assumes tuple: "lpp_stable_numeric_tuple operation (map fst endpoints)
    (map (lpp_stable_endpoint_mode o snd o snd) endpoints)
    (map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints) rho"
    and member: "(coordinate,t,e)\<in>set endpoints"
  shows "lpp_stable_coordinate_value operation (lpp_stable_endpoint_mode e)
    (lp_ieval t eta) (rho coordinate)"
proof -
  obtain i where index: "i<length endpoints" and item: "endpoints!i=(coordinate,t,e)"
    using member by (auto simp: in_set_conv_nth)
  have "lpp_stable_coordinate_value operation
      ((map (lpp_stable_endpoint_mode o snd o snd) endpoints)!i)
      ((map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints)!i)
      (rho ((map fst endpoints)!i))"
    using tuple index by (auto simp: lpp_stable_numeric_tuple_def)
  then show ?thesis by (simp add: index item)
qed

ML \<open>
val checked = [@{thm lpp_stable_endpoint_tuple_exists}, @{thm lpp_stable_numeric_tuple_endpoint}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable endpoint tuple dependency" else ();
\<close>
end
