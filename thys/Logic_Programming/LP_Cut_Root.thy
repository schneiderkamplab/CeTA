theory LP_Cut_Root
  imports LP_Cut_Residual
begin

definition lp_cut_check_root where
  "lp_cut_check_root q modes vs s G guards =
    (length vs=length modes \<and> distinct vs \<and>
     s=[LPCGoals [LPCAtom (Fun (LPCUser q) (map Var vs))]] \<and>
     set G=set (map fst (filter snd (zip vs modes))) \<and> guards=[])"

definition lp_cut_query_env where
  "lp_cut_query_env vs ts x =
    (case map_of (zip vs ts) x of Some t \<Rightarrow> t | None \<Rightarrow> LPIVar x)"

lemma lp_cut_query_env_values:
  assumes len: "length vs=length ts" and distinct: "distinct vs"
  shows "map (lp_cut_query_env vs ts) vs=ts"
proof (rule nth_equalityI)
  show "length (map (lp_cut_query_env vs ts) vs)=length ts" using len by simp
  fix i assume i: "i<length (map (lp_cut_query_env vs ts) vs)"
  have bound: "i<length ts" using i len by simp
  have index: "i<length vs" using i by simp
  show "map (lp_cut_query_env vs ts) vs ! i=ts!i"
    using map_of_zip_nth[OF len distinct bound]
    by (simp add: index lp_cut_query_env_def)
qed

text \<open>The root binds the ordered source program, predicate and input
groundness pattern. Distinct interface variables ensure coverage of every
permitted argument tuple, not merely diagonal or additionally ground queries.\<close>

theorem lp_cut_checked_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) lp_iterm list"
  assumes checked: "lp_cut_check_root q modes vs s G guards"
    and length: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
    and graph: "\<And>\<eta>. lp_cut_knowledge (set G) guards \<eta> \<Longrightarrow>
      SN_on (lp_cut_source P) {lp_cut_state_eval s \<eta>}"
  shows "SN_on (lp_cut_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  let ?env = "lp_cut_query_env vs ts"
  have len: "length vs=length ts" and distinct: "distinct vs"
    using checked length by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env vs=ts" by (rule lp_cut_query_env_values[OF len distinct])
  have ground': "\<forall>(t,b)\<in>set (zip (map ?env vs) modes). b \<longrightarrow> lp_seg_ground t"
    using ground by (simp only: vals)
  have known: "lp_cut_knowledge (set G) guards ?env"
    using checked ground'
    by (auto simp: lp_cut_check_root_def lp_cut_knowledge_def zip_map1)
  have sn: "SN_on (lp_cut_source P) {lp_cut_state_eval s ?env}"
    by (rule graph[OF known])
  show ?thesis using sn checked
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def vals map_map o_def)
qed

lemma root_rejects_shared_query_variables:
  "\<not>lp_cut_check_root q [False,False] [''X'',''X''] s G guards"
  by (simp add: lp_cut_check_root_def)

lemma root_rejects_hidden_groundness:
  "\<not>lp_cut_check_root q [False] [''X''] s [''X''] guards"
  by (simp add: lp_cut_check_root_def)

end
