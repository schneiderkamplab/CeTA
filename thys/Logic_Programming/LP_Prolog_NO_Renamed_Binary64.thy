theory LP_Prolog_NO_Renamed_Binary64
 imports LP_Prolog_NO_Return_Builtin LP_Cut_NO_Ambient_Interface
begin

lemma lpp_machine_term_rename[simp]:
 "lpp_machine_term v\<cdot>(Var \<circ> p) = lpp_machine_term v"
 by (cases v) (simp_all add: lpp_integer_term_def)

lemma lpp_machine_expression_rename[simp]:
 "lpp_machine_expression_term e\<cdot>(Var \<circ> p) = lpp_machine_expression_term e"
 by (induct e) (simp_all add: lpp_machine_term_rename[unfolded o_def])

lemma lpp_machine_unifier_rename:
 assumes inverse: "\<And>x. p (p x) = x"
 shows "lpp_machine_unifier (a\<cdot>(Var \<circ> p)) v =
   map_option (lpc_conjugate_substitution p) (lpp_machine_unifier a v)"
proof (cases a)
 case (Var x)
 have equivalent: "(p y=x) = (y = p x)" for y by (metis inverse)
 have update: "lpc_conjugate_substitution p (Var(x:=lpp_machine_term v)) =
   Var(p x:=lpp_machine_term v)"
   by (rule ext) (simp add: lpc_conjugate_substitution_def fun_upd_def equivalent inverse o_def
     lpp_machine_term_rename[unfolded o_def])
 show ?thesis by (simp add: Var update o_def)
next
 case (Fun f ts)
 have identity: "lpc_conjugate_substitution p Var = Var"
   by (rule ext) (simp add: lpc_conjugate_substitution_def inverse o_def)
 show ?thesis by (cases v) (simp_all add: Fun identity lpp_integer_term_def)
qed

lemma lpp_machine_is_renamed_return_attach:
 assumes evaluated: "lpp_machine_evaluate e=Some v"
   and chosen: "lpp_machine_unifier a v=Some mu"
   and inverse: "\<And>x. p (p x) = x"
   and fixed: "map (\<lambda>t. t\<cdot>lpc_conjugate_substitution p mu) extra = extra"
 shows "(lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a\<cdot>(Var \<circ> p),lpp_machine_expression_term e])#
       map (lp_cut_map (\<lambda>t. t\<cdot>(Var \<circ> p))) gs),
       map (\<lambda>t. t\<cdot>(Var \<circ> p)) payload @ extra)#saved)),
   lpc_attach rest (lpc_return_eval LPIVar
     ((LPCGoals (map (lp_cut_map (\<lambda>t. (t\<cdot>mu)\<cdot>(Var \<circ> p))) gs),
       map (\<lambda>t. (t\<cdot>mu)\<cdot>(Var \<circ> p)) payload @ extra)#saved)))
   \<in> lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback))"
proof -
 let ?r = "Var \<circ> p"
 let ?mu = "lpc_conjugate_substitution p mu"
 have renamed: "lpp_machine_unifier (a\<cdot>?r) v=Some ?mu"
   by (simp only: lpp_machine_unifier_rename[OF inverse] chosen option.map)
 note step = lpp_machine_is_return_attach[OF evaluated renamed,
   of rest "map (lp_cut_map (\<lambda>t. t\<cdot>?r)) gs"
     "map (\<lambda>t. t\<cdot>?r) payload @ extra" saved P fallback]
 show ?thesis using step
   by (simp add: map_map o_def lp_cut_map_comp
     lpc_conjugate_substitution_apply[OF inverse, unfolded o_def] fixed)
qed

ML \<open>
val checked = [@{thm lpp_machine_unifier_rename}, @{thm lpp_machine_is_renamed_return_attach}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted renamed binary64 return dependency" else ();
\<close>
end
