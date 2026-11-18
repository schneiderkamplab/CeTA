theory LP_Prolog_List_Leaf_Program
 imports LP_Prolog_Leaf_Relation_Program LP_Prolog_Forest_Return_Order
begin

text \<open>The proper-list wrapper calls the existing element relation. Its
successful executions preserve the parameter vector, caller environment and
remaining goals. The theorem requires actual element effects; termination of
the element relation does not establish those effects.\<close>

abbreviation lpp_list_observation_nil where
 "lpp_list_observation_nil \<equiv> Fun LPPStructureNode
   [Fun (LPPStructureLabel (LPCUser ''0:prolog_data_5b5d'')) [], lpp_reified_spine []]"
abbreviation lpp_list_observation_cons where
 "lpp_list_observation_cons h t \<equiv> Fun LPPStructureNode
   [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) [], lpp_reified_spine [h,t]]"

definition lpp_list_leaf_clauses :: "string lp_cut_symbol lpp_structure_symbol \<Rightarrow>
 string lp_cut_symbol lpp_structure_symbol \<Rightarrow> nat \<Rightarrow>
 (string lp_cut_symbol lpp_structure_symbol,nat) lp_clause list" where
 "lpp_list_leaf_clauses list_predicate element_rel n = [
  ((list_predicate,[lpp_list_observation_nil,lpp_list_observation_nil]@lpp_leaf_parameters n),[]),
  ((list_predicate,[lpp_list_observation_cons (Var n) (Var (n+1)),
      lpp_list_observation_cons (Var (n+2)) (Var (n+3))]@lpp_leaf_parameters n),
    [(element_rel,[Var n,Var (n+2)]@lpp_leaf_parameters n),
     (list_predicate,[Var (n+1),Var (n+3)]@lpp_leaf_parameters n)])]"

lemma lpp_list_leaf_empty_step:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel (length ps)) \<subseteq> set P"
 shows "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list [])
    (lpp_structural_argument_list []) ps#rest,env),(rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?clause = "((list_predicate,[lpp_list_observation_nil,lpp_list_observation_nil]@lpp_leaf_parameters (length ps)),[])"
 have member: "?clause\<in>set P" using clauses by (auto simp: lpp_list_leaf_clauses_def)
 show ?thesis using lpp_leaf_clause_identity_step[OF member,
   where nu = "lpp_leaf_parameter_env ps (\<lambda>_. env undefined)" and rest = rest and env = env]
  by (simp add: lp_atom_eval_def lpp_leaf_parameters_eval)
qed

lemma lpp_list_leaf_cell_step:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel (length ps)) \<subseteq> set P"
 shows "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list (x#xs))
     (lpp_structural_argument_list (y#ys)) ps#rest,env),
   (lpp_leaf_relation_goal element_rel x y ps#
    lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps#rest,env))\<in>lp_seg_answer_step P"
proof -
 let ?n = "length ps"
 let ?clause = "((list_predicate,[lpp_list_observation_cons (Var ?n) (Var (?n+1)),
      lpp_list_observation_cons (Var (?n+2)) (Var (?n+3))]@lpp_leaf_parameters ?n),
    [(element_rel,[Var ?n,Var (?n+2)]@lpp_leaf_parameters ?n),
     (list_predicate,[Var (?n+1),Var (?n+3)]@lpp_leaf_parameters ?n)])"
 have member: "?clause\<in>set P" using clauses by (auto simp: lpp_list_leaf_clauses_def)
 let ?nu = "lpp_leaf_parameter_env ps (\<lambda>i.
   if i=0 then lp_ieval (lpp_reify_structure x) LPIVar else
   if i=1 then lp_ieval (lpp_reify_structure (lpp_structural_argument_list xs)) LPIVar else
   if i=2 then lp_ieval (lpp_reify_structure y) LPIVar else
    lp_ieval (lpp_reify_structure (lpp_structural_argument_list ys)) LPIVar)"
 show ?thesis using lpp_leaf_clause_identity_step[OF member,where nu = "?nu" and rest = rest and env = env
   and a = "lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list (x#xs))
     (lpp_structural_argument_list (y#ys)) ps"
   and cs = "[lpp_leaf_relation_goal element_rel x y ps,
    lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps]"]
  by (auto simp: lp_atom_eval_def lpp_leaf_parameters_eval lpp_leaf_parameter_local
    lpp_leaf_parameter_env_def)
qed

lemma lpp_list_leaf_program_success:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel (length ps)) \<subseteq> set P"
 and calls: "list_all2 (\<lambda>s t. \<forall>rest.
   ((lpp_leaf_relation_goal element_rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) xs ys"
 shows "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
    (lpp_structural_argument_list ys) ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 using calls
proof (induct arbitrary: rest rule: list_all2_induct)
 case Nil
 show ?case by (rule r_into_rtrancl[OF lpp_list_leaf_empty_step[OF clauses]])
next
 case (Cons x y xs ys)
 have head_path: "((lpp_leaf_relation_goal element_rel x y ps#
    lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps#rest,env),
   (lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps#rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  using Cons.hyps by blast
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF lpp_list_leaf_cell_step[OF clauses]]
   rtrancl_trans[OF head_path Cons.hyps(3)]])
qed


lemma lpp_list_leaf_effect_program_success:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel (length ps)) \<subseteq> set P"
 and element: "\<And>s t rest. lpp_leaf_effect A s t \<Longrightarrow>
   ((lpp_leaf_relation_goal element_rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 and effect: "lpp_leaf_effect A (lpp_structural_argument_list xs) returned"
 shows "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
    returned ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
proof -
 obtain ys where returned: "returned = lpp_structural_argument_list ys"
 and related: "list_all2 (lpp_leaf_effect A) xs ys"
  using effect by (auto simp: lpp_list_leaf_effect_exact)
 have calls: "list_all2 (\<lambda>s t. \<forall>rest.
   ((lpp_leaf_relation_goal element_rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) xs ys"
  using related element by (auto elim: list_all2_mono)
 show ?thesis unfolding returned by (rule lpp_list_leaf_program_success[OF clauses calls])
qed

lemma lpp_list_leaf_program_rejects_variable_spine:
 "\<not> (((list_predicate,[LPIFun LPPStructureLeaf [],output]@ps)#rest,env),next_state)
   \<in>lp_seg_answer_step (lpp_list_leaf_clauses list_predicate element_rel n)"
 by (cases next_state) (auto elim!: lp_seg_answer_step.cases
   simp: lpp_list_leaf_clauses_def lp_iatom_subst_def lp_atom_eval_def
   less_Suc_eq nth_Cons split: nat.splits)


lemma lpp_runtime_forest_return_program:
 assumes clauses: "set (lpp_list_leaf_clauses list_predicate element_rel (length ps)) \<subseteq> set P"
 and element: "\<And>s t rest. lpp_leaf_effect A s t \<Longrightarrow>
   ((lpp_leaf_relation_goal element_rel s t ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 and returned: "lpp_runtime_leaf_effect A (lpp_structural_argument_list xs) returned_tail"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u = {}"
 and observed_head: "lpp_runtime_structure head_value head_shape"
 shows "\<exists>ys. lpp_runtime_structure returned_tail (lpp_structural_argument_list ys) \<and>
   (Inr ys,Inr (head_shape#xs))\<in>lpp_forest_call_order \<and>
   ((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
proof -
 obtain ys where runtime: "lpp_runtime_structure returned_tail (lpp_structural_argument_list ys)"
 and ordered: "(Inr ys,Inr (head_shape#xs))\<in>lpp_forest_call_order"
  using lpp_runtime_returned_argument_tail_decreases[OF returned ground observed_head] by blast
 obtain observed where actual: "lpp_runtime_structure returned_tail observed"
 and effect: "lpp_leaf_effect A (lpp_structural_argument_list xs) observed"
  using returned unfolding lpp_runtime_leaf_effect_def by blast
 have same: "observed = lpp_structural_argument_list ys"
  by (rule lpp_runtime_structure_unique[OF actual runtime])
 have effect_returned: "lpp_leaf_effect A (lpp_structural_argument_list xs) (lpp_structural_argument_list ys)"
  using effect same by simp
 have path: "((lpp_leaf_relation_goal list_predicate (lpp_structural_argument_list xs)
     (lpp_structural_argument_list ys) ps#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  by (rule lpp_list_leaf_effect_program_success[OF clauses element effect_returned])
 show ?thesis by (rule exI[of _ ys])
  (use runtime ordered path in \<open>auto simp: lpp_forest_call_order_def inv_image_def\<close>)
qed

ML \<open>
val checked = @{thms lpp_list_leaf_empty_step lpp_list_leaf_cell_step lpp_list_leaf_program_success
 lpp_list_leaf_effect_program_success lpp_list_leaf_program_rejects_variable_spine lpp_runtime_forest_return_program};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted proper-list leaf program" else ();
\<close>
end
