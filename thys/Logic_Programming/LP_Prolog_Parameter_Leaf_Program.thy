theory LP_Prolog_Parameter_Leaf_Program
 imports LP_Prolog_Leaf_Relation_Program LP_Prolog_Parameter_Leaf_Budget
begin

definition lpp_leaf_atomic_pattern where
 "lpp_leaf_atomic_pattern = Fun LPPStructureNode [Var (1::nat),lpp_reified_spine []]"

definition lpp_leaf_marker_pattern where
 "lpp_leaf_marker_pattern f g payload = Fun LPPStructureNode [Fun (LPPStructureLabel f) [],
   lpp_reified_spine [Fun LPPStructureNode [Fun (LPPStructureLabel g) [],lpp_reified_spine []],payload]]"

definition lpp_parameter_leaf_patterns where
 "lpp_parameter_leaf_patterns f g = [lpp_leaf_marker_pattern f g (Var 0),
   lpp_leaf_marker_pattern f g lpp_leaf_atomic_pattern,lpp_leaf_atomic_pattern,Var 0]"

definition lpp_parameter_leaf_program where
 "lpp_parameter_leaf_program rel spine_predicate f g = lpp_leaf_core_clauses rel spine_predicate 1 @
  map (\<lambda>pattern. ((rel,[Fun LPPStructureLeaf [],pattern,Var 0]),[])) (lpp_parameter_leaf_patterns f g)"

lemma lpp_parameter_leaf_replacement_coverage:
 assumes member: "u\<in>lpp_parameter_leaf_templates f g c"
 shows "\<exists>pattern nu.
   ((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters 1),[])\<in>
     set (lpp_parameter_leaf_program rel spine_predicate f g) \<and>
   map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters 1) =
     [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar] \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure (lpp_structure_template u)) LPIVar"
proof -
 let ?initial = "lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar"
 have input_case: ?thesis if "u = c"
  apply (rule exI[of _ "Var 0"])
  apply (rule exI[of _ "\<lambda>_. ?initial"])
  using that by (simp add: lpp_parameter_leaf_program_def lpp_parameter_leaf_patterns_def
    lpp_leaf_parameters_def)
 have initial_case: ?thesis if "u = Fun f [Fun g [],c]"
  apply (rule exI[of _ "lpp_leaf_marker_pattern f g (Var 0)"])
  apply (rule exI[of _ "\<lambda>_. ?initial"])
  using that by (simp add: lpp_parameter_leaf_program_def lpp_parameter_leaf_patterns_def
    lpp_leaf_parameters_def lpp_leaf_marker_pattern_def)
 have marked_case: ?thesis if "u = Fun f [Fun g [],Fun h []]" for h
  apply (rule exI[of _ "lpp_leaf_marker_pattern f g lpp_leaf_atomic_pattern"])
  apply (rule exI[of _ "\<lambda>i. if i=0 then ?initial else LPIFun (LPPStructureLabel h) []"])
  using that by (simp add: lpp_parameter_leaf_program_def lpp_parameter_leaf_patterns_def
    lpp_leaf_parameters_def lpp_leaf_marker_pattern_def lpp_leaf_atomic_pattern_def)
 have atom_case: ?thesis if "u = Fun h []" for h
  apply (rule exI[of _ lpp_leaf_atomic_pattern])
  apply (rule exI[of _ "\<lambda>i. if i=0 then ?initial else LPIFun (LPPStructureLabel h) []"])
  using that by (simp add: lpp_parameter_leaf_program_def lpp_parameter_leaf_patterns_def
    lpp_leaf_parameters_def lpp_leaf_atomic_pattern_def)
 show ?thesis using member input_case initial_case marked_case atom_case
  unfolding lpp_parameter_leaf_templates_def by blast
qed

lemma lpp_parameter_leaf_program_success:
 assumes effect: "lpp_leaf_effect (lpp_parameter_leaf_templates f g c) s t"
 shows "((lpp_leaf_relation_goal rel s t
   [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar]#rest,env),(rest,env))\<in>
   (lp_seg_answer_step (lpp_parameter_leaf_program rel spine_predicate f g))\<^sup>*"
proof (rule lpp_leaf_relation_success[OF _ _ effect])
 show "set (lpp_leaf_core_clauses rel spine_predicate
   (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])) \<subseteq>
   set (lpp_parameter_leaf_program rel spine_predicate f g)"
  by (simp add: lpp_parameter_leaf_program_def)
next
 fix u assume "u\<in>lpp_parameter_leaf_templates f g c"
 then show "\<exists>pattern nu.
   ((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters
      (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])),[])\<in>
     set (lpp_parameter_leaf_program rel spine_predicate f g) \<and>
   map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters
      (length [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar])) =
     [lp_ieval (lpp_reify_structure (lpp_structure_template c)) LPIVar] \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure (lpp_structure_template u)) LPIVar"
  using lpp_parameter_leaf_replacement_coverage by simp
qed

ML \<open>
val checked = @{thms lpp_parameter_leaf_replacement_coverage lpp_parameter_leaf_program_success};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter leaf program" else ();
\<close>
end
