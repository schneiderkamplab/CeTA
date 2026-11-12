theory LP_Cut_NO_Context_Template
 imports LP_Cut_NO_Ambient_Interface LP_Cut_SEG_Observations
begin

text \<open>Any finite caller continuation can be represented through the
established SEG position templates. Its additional variables are distinct from
the selected call interface. They are explicit coordinates, never the ground
default used for positions outside a return interface.\<close>

lemma lpc_finite_goal_variables:
 "finite (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 by (intro finite_UN_I) auto

lemma lpc_return_context_template:
 fixes gs :: "('f lp_cut_symbol,string) term lp_cut_goal list"
 assumes distinct: "distinct vs"
 shows "\<exists>extra. distinct (vs@extra) \<and> set extra \<inter> set vs = {} \<and>
   (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). vars_term t \<subseteq> set (vs@extra)) \<and>
   map (lp_cut_map (\<lambda>t. lp_ieval (lpc_seg_position_template (vs@extra) t)
     (lpc_return_env (map Var vs @ map Var extra) LPIVar))) gs =
   map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
proof -
 let ?C = "(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t) - set vs"
 let ?extra = "sorted_list_of_set ?C"
 have finite: "finite ?C" using lpc_finite_goal_variables[of gs] by simp
 have contents: "set ?extra = ?C" using finite by simp
 have different: "distinct (vs@?extra)" using distinct contents by simp
 have separate: "set ?extra \<inter> set vs = {}" using contents by blast
 have cover: "vars_term t \<subseteq> set (vs@?extra)"
   if "g\<in>set gs" "t\<in>set (lp_cut_terms g)" for g t
   using contents that by auto
 have observed: "map (lp_cut_map (\<lambda>t. lp_ieval (lpc_seg_position_template (vs@?extra) t)
     (lpc_return_env (map Var vs @ map Var ?extra) LPIVar))) gs =
   map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
 proof (rule map_cong[OF refl], rule lp_cut_goal_map_cong)
   fix g t assume member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)"
   show "lp_ieval (lpc_seg_position_template (vs@?extra) t)
     (lpc_return_env (map Var vs @ map Var ?extra) LPIVar) = lp_ieval t LPIVar"
     using lpc_seg_position_eval[OF different cover[OF member], of LPIVar] by simp
 qed
 show ?thesis by (rule exI[of _ ?extra]) (use different separate cover observed in blast)
qed

ML \<open>
val checked = [@{thm lpc_finite_goal_variables}, @{thm lpc_return_context_template}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted caller context template dependency" else ();
\<close>
end
