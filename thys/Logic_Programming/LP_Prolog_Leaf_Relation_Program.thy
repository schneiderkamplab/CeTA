theory LP_Prolog_Leaf_Relation_Program
 imports LP_Prolog_Bounded_Instantiation LP_Prolog_Reified_Argument_Program
begin

text \<open>The leaf relation is an ordinary shared LP residual. Constructor
and spine clauses preserve the parameter vector; replacement clauses have a
separate coverage premise. All paths below retain the caller environment.\<close>

definition lpp_leaf_parameters where
 "lpp_leaf_parameters n  =  map Var [0..<n]"

definition lpp_leaf_parameter_env where
 "lpp_leaf_parameter_env ps local_values i  = 
  (if i<length ps then ps!i else local_values (i-length ps))"

lemma lpp_leaf_parameters_eval:
 "map (\<lambda>t. lp_ieval t (lpp_leaf_parameter_env ps local_values))
    (lpp_leaf_parameters (length ps))  =  ps"
proof -
 have "map (\<lambda>i. lpp_leaf_parameter_env ps local_values i) [0..<length ps]  = 
   map ((!) ps) [0..<length ps]"
  by (rule map_cong) (auto simp: lpp_leaf_parameter_env_def)
 then show ?thesis by (simp add: lpp_leaf_parameters_def o_def map_nth)
qed

definition lpp_leaf_core_clauses :: "'f lpp_structure_symbol \<Rightarrow> 'f lpp_structure_symbol \<Rightarrow> nat \<Rightarrow>
 ('f lpp_structure_symbol,nat) lp_clause list" where
 "lpp_leaf_core_clauses rel spine_predicate n  =  [
  ((rel,[Fun LPPStructureLeaf [],Fun LPPStructureLeaf []]@lpp_leaf_parameters n),[]),
  ((rel,[Fun LPPStructureNode [Var n,Var (n+1)],
         Fun LPPStructureNode [Var n,Var (n+2)]]@lpp_leaf_parameters n),
     [(spine_predicate,[Var (n+1),Var (n+2)]@lpp_leaf_parameters n)]),
  ((spine_predicate,[Fun LPPStructureNil [],Fun LPPStructureNil []]@lpp_leaf_parameters n),[]),
  ((spine_predicate,[Fun LPPStructureCons [Var n,Var (n+1)],
         Fun LPPStructureCons [Var (n+2),Var (n+3)]]@lpp_leaf_parameters n),
     [(rel,[Var n,Var (n+2)]@lpp_leaf_parameters n),
      (spine_predicate,[Var (n+1),Var (n+3)]@lpp_leaf_parameters n)])]"

lemma lpp_leaf_clause_identity_step:
 assumes member: "(h,bs)\<in>set P"
 and head: "lp_atom_eval h nu = a"
 and body: "map (\<lambda>b. lp_atom_eval b nu) bs = cs"
 shows "((a#rest,env),(cs@rest,env))\<in>lp_seg_answer_step P"
proof -
 obtain c where index: "c<length P" "P!c = (h,bs)"
  using member by (auto simp: in_set_conv_nth)
 show ?thesis using lp_seg_answer_step.resolve[OF index(1), where a = a and \<sigma> = LPIVar
   and \<nu> = nu and gs = rest and \<rho> = env] index(2) head body
  by (simp add: lp_iatom_subst_def)
qed

lemma lpp_leaf_identity_step:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 shows "(((rel,[LPIFun LPPStructureLeaf [],LPIFun LPPStructureLeaf []]@ps)#rest,env),
  (rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?clause  =  "((rel,[Fun LPPStructureLeaf [],Fun LPPStructureLeaf []]@lpp_leaf_parameters (length ps)),[])"
 have member: "?clause\<in>set P" using core by (auto simp: lpp_leaf_core_clauses_def)
 show ?thesis
  using lpp_leaf_clause_identity_step[OF member, where nu = "lpp_leaf_parameter_env ps (\<lambda>_. env undefined)"
    and rest = rest and env = env]
  by (simp add: lp_atom_eval_def lpp_leaf_parameters_eval)
qed

lemma lpp_leaf_spine_empty_step:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 shows "(((spine_predicate,[LPIFun LPPStructureNil [],LPIFun LPPStructureNil []]@ps)#rest,env),
  (rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?clause  =  "((spine_predicate,[Fun LPPStructureNil [],Fun LPPStructureNil []]@lpp_leaf_parameters (length ps)),[])"
 have member: "?clause\<in>set P" using core by (auto simp: lpp_leaf_core_clauses_def)
 show ?thesis
  using lpp_leaf_clause_identity_step[OF member, where nu = "lpp_leaf_parameter_env ps (\<lambda>_. env undefined)"
    and rest = rest and env = env]
  by (simp add: lp_atom_eval_def lpp_leaf_parameters_eval)
qed


lemma lpp_leaf_parameter_local:
 "lpp_leaf_parameter_env ps local_values (length ps+i) = local_values i"
 by (simp add: lpp_leaf_parameter_env_def)

lemma lpp_leaf_constructor_step:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 shows "(((rel,[LPIFun LPPStructureNode [constructor_label,xs],LPIFun LPPStructureNode [constructor_label,ys]]@ps)#rest,env),
   ((spine_predicate,[xs,ys]@ps)#rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?n  =  "length ps"
 let ?clause  =  "((rel,[Fun LPPStructureNode [Var ?n,Var (?n+1)],
   Fun LPPStructureNode [Var ?n,Var (?n+2)]]@lpp_leaf_parameters ?n),
   [(spine_predicate,[Var (?n+1),Var (?n+2)]@lpp_leaf_parameters ?n)])"
 have member: "?clause\<in>set P" using core by (auto simp: lpp_leaf_core_clauses_def)
 let ?nu  =  "lpp_leaf_parameter_env ps (\<lambda>i. if i = 0 then constructor_label else if i = 1 then xs else ys)"
 have parameter_values: "map (\<lambda>t. lp_ieval t ?nu) (lpp_leaf_parameters ?n) = ps"
  by (rule lpp_leaf_parameters_eval)
 show ?thesis using lpp_leaf_clause_identity_step[OF member, where nu = "?nu" and rest = rest and env = env and
    a = "(rel,[LPIFun LPPStructureNode [constructor_label,xs],LPIFun LPPStructureNode [constructor_label,ys]]@ps)"
    and cs = "[(spine_predicate,[xs,ys]@ps)]"]
  by (auto simp: lp_atom_eval_def parameter_values lpp_leaf_parameter_local
    lpp_leaf_parameter_env_def)
qed

lemma lpp_leaf_spine_cell_step:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 shows "(((spine_predicate,[LPIFun LPPStructureCons [a,xs],LPIFun LPPStructureCons [b,ys]]@ps)#rest,env),
   ((rel,[a,b]@ps)#(spine_predicate,[xs,ys]@ps)#rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?n  =  "length ps"
 let ?clause  =  "((spine_predicate,[Fun LPPStructureCons [Var ?n,Var (?n+1)],
   Fun LPPStructureCons [Var (?n+2),Var (?n+3)]]@lpp_leaf_parameters ?n),
   [(rel,[Var ?n,Var (?n+2)]@lpp_leaf_parameters ?n),
    (spine_predicate,[Var (?n+1),Var (?n+3)]@lpp_leaf_parameters ?n)])"
 have member: "?clause\<in>set P" using core by (auto simp: lpp_leaf_core_clauses_def)
 let ?nu  =  "lpp_leaf_parameter_env ps (\<lambda>i. if i = 0 then a else if i = 1 then xs else if i = 2 then b else ys)"
 have parameter_values: "map (\<lambda>t. lp_ieval t ?nu) (lpp_leaf_parameters ?n) = ps"
  by (rule lpp_leaf_parameters_eval)
 show ?thesis using lpp_leaf_clause_identity_step[OF member, where nu = "?nu" and rest = rest and env = env and
    a = "(spine_predicate,[LPIFun LPPStructureCons [a,xs],LPIFun LPPStructureCons [b,ys]]@ps)"
    and cs = "[(rel,[a,b]@ps),(spine_predicate,[xs,ys]@ps)]"]
  by (auto simp: lp_atom_eval_def parameter_values lpp_leaf_parameter_local
    lpp_leaf_parameter_env_def)
qed

lemma lpp_leaf_replacement_step:
 assumes member: "((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters (length ps)),[])\<in>set P"
 and parameter_values: "map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters (length ps)) = ps"
 and replacement: "lp_ieval pattern nu = tree"
 shows "(((rel,[LPIFun LPPStructureLeaf [],tree]@ps)#rest,env),(rest,env))\<in>lp_seg_answer_step P"
 using lpp_leaf_clause_identity_step[OF member, where nu = nu and rest = rest and env = env]
 by (simp add: lp_atom_eval_def parameter_values replacement)


abbreviation lpp_leaf_relation_goal where
 "lpp_leaf_relation_goal rel s t ps \<equiv>
   (rel,[lp_ieval (lpp_reify_structure s) LPIVar,lp_ieval (lpp_reify_structure t) LPIVar]@ps)"

abbreviation lpp_leaf_spine_goal where
 "lpp_leaf_spine_goal spine_predicate xs ys ps \<equiv>
   (spine_predicate,[lp_ieval (lpp_reified_spine (map lpp_reify_structure xs)) LPIVar,
     lp_ieval (lpp_reified_spine (map lpp_reify_structure ys)) LPIVar]@ps)"

lemma lpp_leaf_spine_success:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 and calls: "list_all2 (\<lambda>s t. \<forall>rest.
   ((lpp_leaf_relation_goal rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) xs ys"
 shows "((lpp_leaf_spine_goal spine_predicate xs ys ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 using calls
proof (induct arbitrary: rest rule: list_all2_induct)
 case Nil
 show ?case using r_into_rtrancl[OF lpp_leaf_spine_empty_step[OF core], of rest env] by simp
next
 case (Cons x y xs ys)
 have split_step: "((lpp_leaf_spine_goal spine_predicate (x#xs) (y#ys) ps#rest,env),
   (lpp_leaf_relation_goal rel x y ps#lpp_leaf_spine_goal spine_predicate xs ys ps#rest,env))
    \<in>lp_seg_answer_step P"
  using lpp_leaf_spine_cell_step[OF core] by simp
 have head_path: "((lpp_leaf_relation_goal rel x y ps#lpp_leaf_spine_goal spine_predicate xs ys ps#rest,env),
   (lpp_leaf_spine_goal spine_predicate xs ys ps#rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  using Cons.hyps by blast
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF split_step] rtrancl_trans[OF head_path Cons.hyps(3)]])
qed

lemma lpp_leaf_relation_success:
 assumes core: "set (lpp_leaf_core_clauses rel spine_predicate (length ps)) \<subseteq> set P"
 and replacements: "\<And>u. u\<in>A \<Longrightarrow> \<exists>pattern nu.
   ((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters (length ps)),[])\<in>set P \<and>
   map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters (length ps)) = ps \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure (lpp_structure_template u)) LPIVar"
 and effect: "lpp_leaf_effect A s t"
 shows "((lpp_leaf_relation_goal rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 using effect
proof (induct arbitrary: rest rule: lpp_leaf_effect.induct)
 case unchanged
 show ?case using r_into_rtrancl[OF lpp_leaf_identity_step[OF core], of rest env] by simp
next
 case (replace u)
 obtain pattern nu where member:
   "((rel,[Fun LPPStructureLeaf [],pattern]@lpp_leaf_parameters (length ps)),[])\<in>set P"
  and parameter_values: "map (\<lambda>t. lp_ieval t nu) (lpp_leaf_parameters (length ps)) = ps"
  and evaluated: "lp_ieval pattern nu = lp_ieval (lpp_reify_structure (lpp_structure_template u)) LPIVar"
  using replacements[OF replace.hyps] by blast
 show ?case using r_into_rtrancl[OF lpp_leaf_replacement_step[OF member parameter_values evaluated], of rest env] by simp
next
 case (constructor xs ys f)
 have calls: "list_all2 (\<lambda>s t. \<forall>rest.
   ((lpp_leaf_relation_goal rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) xs ys"
  using constructor by (auto elim: list_all2_mono)
 have split_step: "((lpp_leaf_relation_goal rel (Fun (Inl f) xs) (Fun (Inl f) ys) ps#rest,env),
   (lpp_leaf_spine_goal spine_predicate xs ys ps#rest,env))\<in>lp_seg_answer_step P"
  using lpp_leaf_constructor_step[OF core] by simp
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF split_step] lpp_leaf_spine_success[OF core calls]])
qed

ML \<open>
val checked  =  @{thms lpp_leaf_parameters_eval lpp_leaf_clause_identity_step
 lpp_leaf_identity_step lpp_leaf_spine_empty_step lpp_leaf_parameter_local
 lpp_leaf_constructor_step lpp_leaf_spine_cell_step lpp_leaf_replacement_step
 lpp_leaf_spine_success lpp_leaf_relation_success};
val _  =  if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted leaf relation program" else ();
\<close>
end
