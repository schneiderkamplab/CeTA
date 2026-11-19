theory Global_Boundary_Observation_Check
 imports Global_Boundary_Projection_Check
 "../../thys/Logic_Programming/LP_Prolog_Parameter_Leaf_Prefix"
begin

text \<open>A structural coordinate must encode an observation of the actual
runtime value, with its restricted leaf history. The symbol encoding is explicit;
its concrete correspondence with the native residual remains an obligation.\<close>

definition observed_leaf_coordinate where
 "observed_leaf_coordinate encode A initial_tree runtime_value shadow =
   (\<exists>tree. lpp_runtime_structure runtime_value tree \<and>
    lpp_leaf_effect A initial_tree tree \<and>
    shadow = lp_ieval (map_term encode id (lpp_reify_structure tree)) (\<lambda>_. LPIVar undefined))"

lemma boundary_output_observation_exists:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 and covered: "(hi,initial_tree) \<in> set specs"
 shows "\<exists>shadow. observed_leaf_coordinate encode A initial_tree (eta ''V0'') shadow"
proof -
 obtain frame env where shape: "runtime = [(frame,env)]"
 and helper: "(\<lambda>x. env (Inl x)) = lpc_return_env
   [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''] eta"
  using represented by (auto simp: lpc_reinterface_def lpc_return_eval_def map_eq_Cons_conv)
 have shared: "env (Inr hi) = eta ''V0''"
  using invariant fun_cong[OF helper, of 2]
  by (simp add: shape lpp_observer_output_invariant_def lpp_observer_output_alias_def lpc_return_env_def)
 have effect: "lpp_runtime_leaf_effect A initial_tree (eta ''V0'')"
  using invariant covered
  by (auto simp: shape lpp_observer_output_invariant_def lpp_observer_invariant_def
    lpp_leaf_stack_invariant_def lpc_reinterface_def list_all_iff shared)
 show ?thesis using effect
  by (auto simp: observed_leaf_coordinate_def lpp_runtime_leaf_effect_def)
qed

lemma observed_coordinate_projection:
 assumes first: "observed_leaf_coordinate encode A initial0 (eta x0) (eta s0)"
 and second: "observed_leaf_coordinate encode A initial1 (eta x1) (eta s1)"
 shows "list_all (\<lambda>(initial_tree,value,shadow). observed_leaf_coordinate encode A initial_tree value shadow)
   [(initial0, (map eta [x0,x1,s0,s1]) ! 0, (map eta [x0,x1,s0,s1]) ! 2),
    (initial1, (map eta [x0,x1,s0,s1]) ! 1, (map eta [x0,x1,s0,s1]) ! 3)]"
 using first second by simp

lemma leaf_shadow_cannot_describe_constructor:
 fixes f :: nat
 shows
 "\<not> observed_leaf_coordinate id A initial_tree (LPIFun f [] :: (nat,string) lp_iterm)
   (LPIFun LPPStructureLeaf [] :: (nat lpp_structure_symbol,string) lp_iterm)"
proof
 assume bad: "observed_leaf_coordinate id A initial_tree (LPIFun f [] :: (nat,string) lp_iterm) (LPIFun LPPStructureLeaf [] :: (nat lpp_structure_symbol,string) lp_iterm)"
 obtain template :: "(nat,string) term" where runtime_eq: "LPIFun f [] = lp_ieval template LPIVar"
 and shadow_eq: "(LPIFun LPPStructureLeaf [] :: (nat lpp_structure_symbol,string) lp_iterm) =
   lp_ieval (map_term id id (lpp_reify_structure (lpp_structure_template template))) (\<lambda>_. LPIVar undefined)"
  using bad by (auto simp: observed_leaf_coordinate_def lpp_runtime_structure_def)
 show False using runtime_eq shadow_eq by (cases template) auto
qed

lemma variable_leaf_observation_positive:
 "observed_leaf_coordinate id (A::(nat,string) term set) (Fun (Inr ()) [])
   (LPIVar ''x'') (LPIFun LPPStructureLeaf [] :: (nat lpp_structure_symbol,string) lp_iterm)"
proof -
 have leaf: "lpp_leaf_effect A (Fun (Inr ()) []) (Fun (Inr ()) [])"
  using lpp_template_leaf_effect_reflexive[of A "Var (''x'')"] by simp
 have observed: "lpp_runtime_structure (LPIVar ''x'' :: (nat,string) lp_iterm) (Fun (Inr ()) [])"
  unfolding lpp_runtime_structure_def by (rule exI[of _ "Var ''x''"]) simp
 show ?thesis using leaf observed
  by (auto simp: observed_leaf_coordinate_def)
qed

ML \<open>
val checked = @{thms boundary_output_observation_exists observed_coordinate_projection
 leaf_shadow_cannot_describe_constructor variable_leaf_observation_positive};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted global boundary observation" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-boundary-observation/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Native encoding and family initialization remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_BOUNDARY_OBSERVATION_KERNEL_CHECKED";
\<close>
end
