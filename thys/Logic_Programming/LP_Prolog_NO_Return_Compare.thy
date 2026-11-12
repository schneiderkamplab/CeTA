theory LP_Prolog_NO_Return_Compare
 imports LP_Prolog_NO_Return_Is
begin

definition lpp_no_return_comparison_value where
 "lpp_no_return_comparison_value f left right held =
   (case (lpp_source_comparison f,lpp_machine_evaluate left,lpp_machine_evaluate right) of
     (Some (comparison,reversed),Some x,Some y) \<Rightarrow>
       held=lpp_integer_compare comparison
         (fst (lpp_machine_fraction (if reversed then y else x)) * snd (lpp_machine_fraction (if reversed then x else y)))
         (fst (lpp_machine_fraction (if reversed then x else y)) * snd (lpp_machine_fraction (if reversed then y else x)))
     | _ \<Rightarrow> False)"

fun lpp_no_return_compare where
 "lpp_no_return_compare left right held
   ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),payload)#saved) tt =
   (a=lpp_machine_expression_term left \<and> b=lpp_machine_expression_term right \<and>
    lpp_no_return_comparison_value f left right held \<and> tt=(if held then (LPCGoals gs,payload)#saved else saved))"
| "lpp_no_return_compare left right held ss tt = False"

lemma lpp_no_return_compare_sound:
 assumes checked: "lpp_no_return_compare left right held ss tt"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),lpc_attach rest (lpc_return_eval LPIVar tt))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 using checked
proof (induct left right held ss tt rule: lpp_no_return_compare.induct)
 case (1 left right held f a b gs payload saved tt)
 then obtain comparison reversed x y where name: "lpp_source_comparison f=Some (comparison,reversed)"
   and left: "lpp_machine_evaluate left=Some x" and right: "lpp_machine_evaluate right=Some y"
   and a: "a=lpp_machine_expression_term left" and b: "b=lpp_machine_expression_term right"
   and held: "held=lpp_integer_compare comparison
     (fst (lpp_machine_fraction (if reversed then y else x)) * snd (lpp_machine_fraction (if reversed then x else y)))
     (fst (lpp_machine_fraction (if reversed then x else y)) * snd (lpp_machine_fraction (if reversed then y else x)))"
   and tt: "tt=(if held then (LPCGoals gs,payload)#saved else saved)"
   by (auto simp: lpp_no_return_comparison_value_def split: option.splits prod.splits)
 have descriptor: "lpp_comparison_descriptor f comparison reversed"
   using name lpp_source_comparison_descriptor by blast
 show ?case using lpp_machine_comparison_return_attach[OF descriptor left right held,
   of rest gs payload saved P fallback] by (simp add: a b tt)
qed simp_all

fun lpp_no_return_integer where
 "lpp_no_return_integer v ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),payload)#saved) tt =
   (f=''1:integer'' \<and> a=lpp_machine_term v \<and> lpp_machine_valid v \<and>
    tt=(if lpp_machine_is_integer v then (LPCGoals gs,payload)#saved else saved))"
| "lpp_no_return_integer v ss tt = False"

lemma lpp_machine_integer_return_attach:
 assumes valid: "lpp_machine_valid v"
 shows "(lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [lpp_machine_term v])#gs),payload)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar
     (if lpp_machine_is_integer v then (LPCGoals gs,payload)#saved else saved)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 have selected: "(''1:integer'',length [lpp_machine_value v])\<in>lpp_builtin_signature"
   by (simp add: lpp_builtin_signature_def)
 note outcome = lpp_machine_integer_test[OF valid, of "lpp_binary64_profile_operation fallback"]
 note step = lpp_return_boolean_attach_source[where U="lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)"
   and f="''1:integer''" and input_terms="[lpp_machine_value v]" and held="lpp_machine_is_integer v",
   OF selected outcome, of rest "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs"
     "lpc_return_env payload LPIVar" "lpc_return_eval LPIVar saved" P]
 show ?thesis using step by (cases "lpp_machine_is_integer v")
   (simp_all add: lpc_return_eval_def lpp_machine_term_eval)
qed

lemma lpp_no_return_integer_sound:
 "lpp_no_return_integer v ss tt \<Longrightarrow>
   (lpc_attach rest (lpc_return_eval LPIVar ss),lpc_attach rest (lpc_return_eval LPIVar tt))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof (induct v ss tt rule: lpp_no_return_integer.induct)
 case (1 v f a gs payload saved tt)
 then have f: "f=''1:integer''" and a: "a=lpp_machine_term v"
   and valid: "lpp_machine_valid v"
   and target: "tt=(if lpp_machine_is_integer v then (LPCGoals gs,payload)#saved else saved)" by auto
 show ?case unfolding f a target by (rule lpp_machine_integer_return_attach[OF valid])
qed simp_all

ML \<open>
val checked = [@{thm lpp_no_return_compare_sound}, @{thm lpp_no_return_integer_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked binary64 return guards" else ();
\<close>
end
