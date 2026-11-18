theory LP_Prolog_Return_Slot_Controls
 imports LP_Prolog_Return_Slot_Univ LP_Prolog_Leaf_Lexicographic_Return
begin

lemma lpp_return_slot_names_distinct:
 "lpp_return_slot_name i=lpp_return_slot_name j \<longleftrightarrow> i=j"
proof
 assume equal: "lpp_return_slot_name i=lpp_return_slot_name j"
 have "length (lpp_return_slot_name i)=length (lpp_return_slot_name j)"
  by (rule arg_cong[OF equal])
 then show "i=j" by simp
next
 assume "i=j" then show "lpp_return_slot_name i=lpp_return_slot_name j" by simp
qed

lemma lpp_nonground_constructor_not_ground_leaf_return:
 fixes f :: "'f" and z :: string
 shows "\<not>lpp_runtime_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) (LPIFun f [LPIVar z])"
proof
 assume effect: "lpp_runtime_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) (LPIFun f [LPIVar z])"
 have observed: "lpp_runtime_structure (LPIFun f [LPIVar z]) (Fun (Inl f) [Fun (Inr ()) []])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Fun f [Var z]"]) simp
 obtain current where runtime: "lpp_runtime_structure (LPIFun f [LPIVar z]) current"
  and leaf: "lpp_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) current"
  using effect by (auto simp: lpp_runtime_leaf_effect_def)
 have same: "current=Fun (Inl f) [Fun (Inr ()) []]"
  by (rule lpp_runtime_structure_unique[OF runtime observed])
 have relation: "lpp_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) (Fun (Inl f) [Fun (Inr ()) []])"
  using leaf by (simp only: same)
 have ground: "vars_term u={}" if "u\<in>{u::('f,string) term. vars_term u={}}" for u
  using that by simp
 show False using lpp_ground_leaf_effect_rigidity[OF relation ground] by simp
qed

lemma lpp_unprotected_output_leaf_counterexample:
 fixes x y z :: string and f a pair_symbol :: "'f"
 assumes different: "x\<noteq>y" "x\<noteq>z" "y\<noteq>z"
 defines "sigma \<equiv> LPIVar(x:=LPIFun f [LPIVar z],y:=LPIFun a [])"
 shows "lpc_mgu_unify (LPIFun pair_symbol [LPIVar x,LPIVar y])
    (LPIFun pair_symbol [LPIFun f [LPIVar z],LPIFun a []]) [LPCAtom (LPIVar x)] sigma \<and>
   \<not>lpp_runtime_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) (lp_isubst (LPIVar x) sigma)"
proof -
 have mgu: "lpc_mgu_unify (LPIFun pair_symbol [LPIVar x,LPIVar y])
    (LPIFun pair_symbol [LPIFun f [LPIVar z],LPIFun a []]) [LPCAtom (LPIVar x)] sigma"
  using different unfolding sigma_def lpc_mgu_unify_def by auto
 have rejected: "\<not>lpp_runtime_leaf_effect {u::('f,string) term. vars_term u={}} (Fun (Inr ()) []) (lp_isubst (LPIVar x) sigma)"
  using lpp_nonground_constructor_not_ground_leaf_return[of f z] different
  by (simp add: sigma_def)
 show ?thesis using mgu rejected by simp
qed

ML \<open>
val checked = @{thms lpp_return_slot_names_distinct lpp_nonground_constructor_not_ground_leaf_return
 lpp_unprotected_output_leaf_counterexample};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted return-slot controls" else ();
\<close>
end
