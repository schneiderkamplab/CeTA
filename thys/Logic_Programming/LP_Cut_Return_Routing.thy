theory LP_Cut_Return_Routing
  imports LP_Cut_Return_Interface
begin

definition lpc_return_route where
  "lpc_return_route bindings x = (case map_of bindings x of Some i \<Rightarrow> i | None \<Rightarrow> 0)"

definition lpc_check_return_route where
  "lpc_check_return_route bindings interface =
    list_all (\<lambda>(x,i). i<length interface \<and> interface!i=Var x) bindings"

lemma lpc_return_route_value:
  assumes checked: "lpc_check_return_route bindings interface"
    and bound: "x\<in>dom (map_of bindings)"
  shows "lpc_return_env interface eta (lpc_return_route bindings x)=eta x"
proof -
  obtain i where lookup: "map_of bindings x=Some i" using bound by auto
  have member: "(x,i)\<in>set bindings" by (rule map_of_SomeD[OF lookup])
  have valid: "i<length interface" and entry_value: "interface!i=Var x"
    using checked member by (auto simp: lpc_check_return_route_def list_all_iff)
  show ?thesis by (simp add: lpc_return_route_def lookup lpc_return_env_def valid entry_value)
qed

lemma lpc_return_route_term:
  assumes checked: "lpc_check_return_route bindings interface"
    and covered: "vars_term t \<subseteq> dom (map_of bindings)"
  shows "lp_ieval (map_term id (lpc_return_route bindings) t) (lpc_return_env interface eta) =
    lp_ieval t eta"
  using covered
  by (induct t) (auto simp: lpc_return_route_value[OF checked] intro!: map_cong)

definition lpc_check_return_route_goals where
  "lpc_check_return_route_goals bindings interface gs =
    (lpc_check_return_route bindings interface \<and>
     (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> dom (map_of bindings)))"

lemma lpc_return_route_goals:
  assumes "lpc_check_return_route_goals bindings interface gs"
  shows "map (lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env interface eta)))
      (map (lp_cut_map (map_term id (lpc_return_route bindings))) gs) =
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
proof -
  have local: "lp_cut_map (\<lambda>t. lp_ieval t (lpc_return_env interface eta))
      (lp_cut_map (map_term id (lpc_return_route bindings)) g) =
    lp_cut_map (\<lambda>t. lp_ieval t eta) g" if "g\<in>set gs" for g
  proof -
    have checked: "lpc_check_return_route bindings interface"
      and covered: "\<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> dom (map_of bindings)"
      using assms that by (auto simp: lpc_check_return_route_goals_def)
    show ?thesis using covered by (cases g)
      (auto intro!: lpc_return_route_term[OF checked])
  qed
  show ?thesis using local by (simp add: map_map o_def cong: map_cong)
qed

end
