theory Actual_Global_Arithmetic_Check
 imports Global_Arithmetic_Path_Check
 "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Arithmetic_Node"
begin

lemma actual_arithmetic_normalization_global_path:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and encode :: "(string lp_cut_symbol) lpp_structure_symbol \<Rightarrow> string lp_cut_symbol"
 assumes shape: "runtime = (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [eta x,expression])#gs),env)#saved"
 and invariant: "lpp_observer_output_invariant A specs rest oi hi runtime"
 and actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation) runtime event tt"
 and nonempty: "tt \<noteq> []"
 and observed: "observed_leaf_coordinate encode A initial_tree (eta x) (eta sx)"
 and arithmetic: "((arithmetic_symbol,map Var [x,p,sx,sp]),
   [(boundary_symbol,map Var [x,z,p,sx,sz,sp])]) \<in> set Q"
 and projection: "((boundary_symbol,map Var [v0,v1,v2,t0,t1,t2]),
   [(equality_symbol,map Var [v0,v1,t0,t1])]) \<in> set Q"
 and distinct: "distinct [v0,v1,v2,t0,t1,t2]"
 and fresh: "z \<notin> {x,p,sx,sp}" "sz \<notin> {x,p,sx,sp}" "z \<noteq> sz"
 shows "event = None \<and> (\<exists>scalar shadow.
   lpp_stable_scalar_evaluation operation expression (LPIFun (LPCUser scalar) []) \<and>
   lpc_answer_transition P ((LPCGoals (LPCUnify (eta x) (LPIFun (LPCUser scalar) [])#gs),env)#saved) event tt \<and>
   lpp_observer_output_invariant A specs rest oi hi
    ((LPCGoals (LPCUnify (eta x) (LPIFun (LPCUser scalar) [])#gs),env)#saved) \<and>
   observed_leaf_coordinate encode A (Fun (Inl (LPCUser scalar)) []) (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow \<and>
   ([(arithmetic_symbol,map eta [x,p,sx,sp])],
    [(equality_symbol,[eta x,LPIFun (LPCUser scalar) [],eta sx,shadow])]) \<in> (lp_ild Q)\<^sup>+ \<and>
   observed_leaf_coordinate encode A initial_tree (eta x) (eta sx))"
proof -
 obtain scalar where no_event: "event = None"
 and evaluated: "lpp_stable_scalar_evaluation operation expression (LPIFun (LPCUser scalar) [])"
 and equality: "lpc_answer_transition P
   ((LPCGoals (LPCUnify (eta x) (LPIFun (LPCUser scalar) [])#gs),env)#saved) event tt"
  using lpp_univ_is_uses_shared_equality[OF actual[unfolded shape]] nonempty by blast
 have normalized: "lpp_observer_output_invariant A specs rest oi hi
   ((LPCGoals (LPCUnify (eta x) (LPIFun (LPCUser scalar) [])#gs),env)#saved)"
  using invariant by (auto simp: shape lpp_observer_output_invariant_def lpp_observer_output_alias_def
    lpp_observer_invariant_def lpc_reinterface_def lpc_attach_answers_def
    lpp_finite_execution_def lpp_finite_goals_def lpp_leaf_stack_invariant_def)
 obtain shadow where scalar_observed: "observed_leaf_coordinate encode A (Fun (Inl (LPCUser scalar)) [])
   (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow"
 and path: "([(arithmetic_symbol,map eta [x,p,sx,sp])],
   [(equality_symbol,[eta x,LPIFun (LPCUser scalar) [],eta sx,shadow])]) \<in> (lp_ild Q)\<^sup>+"
  using arithmetic_to_equality_observed_path[OF arithmetic projection distinct fresh observed, of "LPCUser scalar"] by blast
 show ?thesis using no_event evaluated equality normalized scalar_observed path observed by blast
qed

ML \<open>
val checked = @{thms actual_arithmetic_normalization_global_path};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted actual arithmetic/global path" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-actual-global-arithmetic/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Equality successor and full-family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACTUAL_GLOBAL_ARITHMETIC_KERNEL_CHECKED";
\<close>
end
