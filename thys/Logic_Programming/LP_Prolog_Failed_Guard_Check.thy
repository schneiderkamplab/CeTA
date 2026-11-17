theory LP_Prolog_Failed_Guard_Check
 imports LP_Prolog_Failed_Guard_Clause
begin

fun lpp_check_tree_failure where
 "lpp_check_tree_failure P q observations d (H,tree) =
   (d<length P \<and> distinct H \<and> length H=length observations \<and>
    fst (P!d)=Fun (LPCUser q) (map Var H) \<and>
    take (length (lpp_failed_tree_goals tree)) (snd (P!d)) =
      lpp_failed_tree_goals tree \<and>
    lpp_failed_tree_check (lpp_scalar_value_table H observations) tree)"

lemma lpp_check_tree_failure_sound:
 assumes checked: "lpp_check_tree_failure P q observations d receipt"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain H tree where receipt: "receipt=(H,tree)" by (cases receipt) auto
 let ?table = "lpp_scalar_value_table H observations"
 let ?eta = "lpp_partial_arguments H actuals"
 let ?remaining = "drop (length (lpp_failed_tree_goals tree)) (snd (P!d))"
 have index: "d<length P" and distinct: "distinct H" and lengths: "length H=length observations"
   and failed: "lpp_failed_tree_check ?table tree"
   using checked by (auto simp: receipt)
 have clause: "P!d=(Fun (LPCUser q) (map Var H),
      lpp_failed_tree_goals tree @ ?remaining)"
   using checked append_take_drop_id[of "length (lpp_failed_tree_goals tree)" "snd (P!d)"]
   by (cases "P!d") (auto simp: receipt)
 have actual_length: "length H=length actuals" using observed lengths
   by (simp add: lpp_scalar_observations_def)
 have head: "lp_ieval (Fun (LPCUser q) (map Var H)) ?eta = LPIFun (LPCUser q) actuals"
   using lpp_partial_arguments_exact[OF actual_length distinct] by (simp add: map_map o_def)
 have parameters: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (?eta x) (lpp_machine_value w)" if "?table x=Some w" for x w
   by (rule lpp_scalar_observed_argument[OF lengths distinct observed that])
 have covered: "x\<in>set H" if "?table x=Some w" for x w
   by (rule lpp_scalar_table_covered[OF lengths that])
 have source: "(LPCClause (LPCAtom (lp_ieval (Fun (LPCUser q) (map Var H)) ?eta)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
   by (rule lpp_failed_tree_clause[where value_table="?table", OF index clause failed])
     (use parameters covered in auto)
 show ?thesis using source head by simp
qed

end
