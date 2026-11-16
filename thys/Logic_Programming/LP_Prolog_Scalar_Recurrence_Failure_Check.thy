theory LP_Prolog_Scalar_Recurrence_Failure_Check
 imports LP_Prolog_Scalar_Recurrence_Interface
begin

fun lpp_check_scalar_failure where
 "lpp_check_scalar_failure P q observations d (H,guards,failure) =
   (d<length P \<and> distinct H \<and> length H=length observations \<and>
    fst (P!d)=Fun (LPCUser q) (map Var H) \<and>
    take (Suc (length guards)) (snd (P!d)) =
      map lpp_scalar_guard_goal guards @ [lpp_scalar_guard_goal failure] \<and>
    list_all (\<lambda>g. lpp_scalar_guard_check (lpp_scalar_value_table H observations) g=Some True) guards \<and>
    lpp_scalar_guard_check (lpp_scalar_value_table H observations) failure=Some False)"

lemma lpp_check_scalar_failure_sound:
 assumes checked: "lpp_check_scalar_failure P q observations d receipt"
   and observed: "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations actuals"
 shows "(LPCClause (LPCAtom (LPIFun (LPCUser q) actuals)#gs) d mark#saved,saved)\<in>
   (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
proof -
 obtain H guards failure where receipt: "receipt=(H,guards,failure)" by (cases receipt) auto
 let ?table = "lpp_scalar_value_table H observations"
 let ?eta = "lpp_partial_arguments H actuals"
 let ?remaining = "drop (Suc (length guards)) (snd (P!d))"
 have index: "d<length P" and distinct: "distinct H" and lengths: "length H=length observations"
   and successful: "list_all (\<lambda>g. lpp_scalar_guard_check ?table g=Some True) guards"
   and failed: "lpp_scalar_guard_check ?table failure=Some False"
   using checked by (auto simp: receipt)
 have clause: "P!d=(Fun (LPCUser q) (map Var H),
      map lpp_scalar_guard_goal guards @ lpp_scalar_guard_goal failure # ?remaining)"
   using checked append_take_drop_id[of "Suc (length guards)" "snd (P!d)"]
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
   by (rule lpp_scalar_failed_clause[where value_table="?table", OF index clause successful failed])
     (use parameters covered in auto)
 show ?thesis using source head by simp
qed

ML \<open>
val checked = [@{thm lpp_check_scalar_failure_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar recurrence failure receipt dependency" else ();
\<close>
end
