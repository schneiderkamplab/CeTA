theory LP_Cut_Rational_NO_Steps
  imports LP_Cut_Rational_Goals LP_Cut_NO_Pending
begin

abbreviation lpc_rational_state where
  "lpc_rational_state G s \<equiv> lp_cut_state_map (lp_rational_graph_value G LPIVar) s"

definition lpc_rational_resolve where
  "lpc_rational_resolve fuel G P i gs c m es env body successor =
    (lp_rational_graph_closed G \<and> i<length G \<and> c<length P \<and>
     lp_rational_match fuel G env (fst (P!c)) i \<and>
     (\<forall>g\<in>set (snd (P!c)). \<forall>t\<in>set (lp_cut_terms g). vars_term t\<subseteq>vars_term (fst (P!c))) \<and>
     list_all2 (lpc_rational_goal_match fuel G env)
       (map (lp_cut_bind m id) (snd (P!c))) body \<and>
     successor=LPCGoals (body@gs)#es)"

lemma lpc_rational_resolve_sound:
  assumes checked: "lpc_rational_resolve fuel G P i gs c m es env body successor"
  shows "(lpc_rational_state G (LPCClause (LPCAtom i#gs) c m#es),
    lpc_rational_state G successor)\<in>lp_cut_mgu_source P"
proof -
  have closed: "lp_rational_graph_closed G" and index: "i<length G" and clause: "c<length P"
    and matched: "lp_rational_match fuel G env (fst (P!c)) i"
    and vars: "\<And>g t. g\<in>set (snd (P!c)) \<Longrightarrow> t\<in>set (lp_cut_terms g) \<Longrightarrow>
      vars_term t\<subseteq>vars_term (fst (P!c))"
    and body: "list_all2 (lpc_rational_goal_match fuel G env)
       (map (lp_cut_bind m id) (snd (P!c))) body"
    using checked by (auto simp: lpc_rational_resolve_def)
  have mgu: "lpc_mgu_resolve (lp_rational_graph_value G LPIVar i)
    (map (lp_cut_map (lp_rational_graph_value G LPIVar)) gs)
    (fst (P!c)) (snd (P!c)) LPIVar (lp_rational_match_env G LPIVar env)"
    by (rule lpc_closed_match_most_general[OF lp_rational_closed_value_subst[OF closed index]
      lp_rational_match_sound[OF matched] vars])
  show ?thesis using lp_cut_mgu_source.resolve[OF clause mgu, of m "lpc_rational_state G es"]
    lpc_rational_body_match_sound[OF body, of LPIVar] checked
    by (simp add: lpc_rational_resolve_def lp_cut_state_map_def map_map o_def lp_cut_map_comp)
qed

lemma lpc_rational_backtrack_sound:
  fixes P :: "('a,string) lp_cut_program"
  assumes "lp_rational_graph_closed G" "i<length G" "c<length P"
    "lp_rational_head_clash fuel G i (fst (P!c)) evidence"
  shows "(lpc_rational_state G (LPCClause (LPCAtom i#gs) c m#es),
    lpc_rational_state G es)\<in>lp_cut_mgu_source P"
proof -
  have clash: "\<not>(\<exists>sigma :: string \<Rightarrow> ('a lp_cut_symbol,string) lp_iterm.
      \<exists>eta. lp_isubst (lp_rational_graph_value G LPIVar i) sigma=lp_ieval (fst (P!c)) eta)"
    by (rule lp_rational_head_clash_no_unifier[OF assms(1,2,4)])
  show ?thesis using lp_cut_mgu_source.backtrack[OF assms(3) clash,
    where m=m and gs="map (lp_cut_map (lp_rational_graph_value G LPIVar)) gs"
      and es="lpc_rational_state G es"]
    by (simp add: lp_cut_state_map_def)
qed
end
