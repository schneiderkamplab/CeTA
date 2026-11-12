theory LP_Prolog_NO_Renamed_Machine
 imports LP_Prolog_NO_Renamed_Ordinary LP_Prolog_NO_Renamed_Binary64
begin

fun lpp_no_return_is_support where
 "lpp_no_return_is_support ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),payload)#saved) = vars_term a"
| "lpp_no_return_is_support ss = {}"

lemma lpp_no_return_is_support_finite[simp]:
 "finite (lpp_no_return_is_support ss)"
 by (induct ss rule: lpp_no_return_is_support.induct) simp_all

lemma lpp_machine_unifier_support:
 assumes chosen: "lpp_machine_unifier a v=Some mu" and outside: "z\<notin>vars_term a"
 shows "mu z=Var z"
 using chosen outside by (cases a) (auto split: if_splits)

lemma lpp_no_return_is_renamed_sound:
 assumes checked: "lpp_no_return_is e ss tt"
   and inverse: "\<And>x. p (p x) = x"
   and safe: "(\<Union>t\<in>set extra. vars_term t) \<inter> p ` lpp_no_return_is_support ss = {}"
 shows "(lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra ss)),
   lpc_attach rest (lpc_return_eval LPIVar (lpc_no_rename_rows p extra tt)))
   \<in>lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
 using checked safe
proof (induct e ss tt rule: lpp_no_return_is.induct)
 case (1 e f a b gs payload saved tt)
 then obtain v where f: "f=''2:is''" and b: "b=lpp_machine_expression_term e"
   and evaluated: "lpp_machine_evaluate e=Some v"
   and target: "tt=(case lpp_machine_unifier a v of None \<Rightarrow> saved | Some mu \<Rightarrow>
     (LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>mu)) gs),map (\<lambda>t. t\<cdot>mu) payload)#saved)"
   by (auto split: option.splits)
 have outside: "z\<notin>p ` vars_term a" if "z\<in>\<Union>(vars_term ` set extra)" for z
   using 1 that by auto
 show ?case
 proof (cases "lpp_machine_unifier a v")
   case None
   have rejected: "lpp_machine_unifier (a\<cdot>(Var \<circ> p)) v=None"
     by (simp only: lpp_machine_unifier_rename[OF inverse] None option.map)
   note step = lpp_machine_is_return_failure_attach[where rest=rest
     and gs="map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs"
     and payload="map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra"
     and saved="lpc_no_rename_rows p extra saved" and P=P and fallback=fallback,
     OF evaluated rejected]
   show ?thesis using step by (simp add: f b target None lpc_no_rename_rows_def
     lpp_machine_expression_rename[unfolded o_def])
 next
   case (Some mu)
   have fixed: "map (\<lambda>t. t\<cdot>lpc_conjugate_substitution p mu) extra=extra"
     by (rule lpc_substitution_fixes_ambient_terms,
       rule lpc_conjugate_supported_outside[where S="vars_term a" and substitution=mu, OF inverse],
       rule lpp_machine_unifier_support[OF Some], assumption, rule outside)
   note step = lpp_machine_is_renamed_return_attach[where rest=rest and gs=gs and payload=payload
     and saved="lpc_no_rename_rows p extra saved" and P=P and fallback=fallback,
     OF evaluated Some inverse fixed]
   show ?thesis using step by (simp add: f b target Some lpc_no_rename_rows_def map_map o_def lp_cut_map_comp
     lpp_machine_expression_rename[unfolded o_def])
 qed
qed simp_all

lemma lpp_no_return_compare_renamed:
 "lpp_no_return_compare left right held ss tt \<Longrightarrow>
   lpp_no_return_compare left right held (lpc_no_rename_rows p extra ss) (lpc_no_rename_rows p extra tt)"
 by (induct left right held ss tt rule: lpp_no_return_compare.induct)
   (auto simp: lpc_no_rename_rows_def lpp_machine_expression_rename[unfolded o_def])

lemma lpp_no_return_integer_renamed:
 "lpp_no_return_integer v ss tt \<Longrightarrow>
   lpp_no_return_integer v (lpc_no_rename_rows p extra ss) (lpc_no_rename_rows p extra tt)"
 by (induct v ss tt rule: lpp_no_return_integer.induct)
   (auto simp: lpc_no_rename_rows_def lpp_machine_term_rename[unfolded o_def])

ML \<open>
val checked = [@{thm lpp_machine_unifier_support}, @{thm lpp_no_return_is_renamed_sound},
 @{thm lpp_no_return_compare_renamed}, @{thm lpp_no_return_integer_renamed}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted uniformly renamed machine actions" else ();
\<close>
end
