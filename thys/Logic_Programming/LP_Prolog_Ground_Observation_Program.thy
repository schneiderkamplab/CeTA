theory LP_Prolog_Ground_Observation_Program
 imports LP_Prolog_Leaf_Relation_Program LP_Prolog_Leaf_Effect_Composition
begin

text \<open>Ground runtime values have observations without variable leaves.
This recognizer retains that property as a successful-prefix obligation in the
shared LP semantics. Groundness of the reified data alone is insufficient.\<close>

definition lpp_ground_observation_program ::
 "'f lpp_structure_symbol \<Rightarrow> 'f lpp_structure_symbol \<Rightarrow>
  ('f lpp_structure_symbol,nat) lp_clause list" where
 "lpp_ground_observation_program tree_predicate spine_predicate = [
  ((tree_predicate,[Fun LPPStructureNode [Var 0,Var 1]]),[(spine_predicate,[Var 1])]),
  ((spine_predicate,[Fun LPPStructureNil []]),[]),
  ((spine_predicate,[Fun LPPStructureCons [Var 0,Var 1]]),
   [(tree_predicate,[Var 0]),(spine_predicate,[Var 1])])]"

lemma lpp_ground_observation_node_step:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 shows "(((p,[LPIFun LPPStructureNode [constructor_label,xs]])#rest,env),
   ((q,[xs])#rest,env))\<in>lp_seg_answer_step P"
proof -
 have member: "((p,[Fun LPPStructureNode [Var 0,Var 1]]),[(q,[Var 1])])\<in>set P"
  using core by (auto simp: lpp_ground_observation_program_def)
 show ?thesis using lpp_leaf_clause_identity_step[OF member,
  where nu = "\<lambda>i. if i=0 then constructor_label else xs" and rest = rest and env = env]
  by (force simp: lp_atom_eval_def)
qed

lemma lpp_ground_observation_nil_step:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 shows "(((q,[LPIFun LPPStructureNil []])#rest,env),(rest,env))\<in>lp_seg_answer_step P"
proof -
 have member: "((q,[Fun LPPStructureNil []]),[])\<in>set P"
  using core by (auto simp: lpp_ground_observation_program_def)
 show ?thesis using lpp_leaf_clause_identity_step[OF member,
  where nu = "\<lambda>_. env undefined" and rest = rest and env = env]
  by (force simp: lp_atom_eval_def)
qed

lemma lpp_ground_observation_cons_step:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 shows "(((q,[LPIFun LPPStructureCons [a,xs]])#rest,env),
   ((p,[a])#(q,[xs])#rest,env))\<in>lp_seg_answer_step P"
proof -
 have member: "((q,[Fun LPPStructureCons [Var 0,Var 1]]),[(p,[Var 0]),(q,[Var 1])])\<in>set P"
  using core by (auto simp: lpp_ground_observation_program_def)
 show ?thesis using lpp_leaf_clause_identity_step[OF member,
  where nu = "\<lambda>i. if i=0 then a else xs" and rest = rest and env = env]
  by (force simp: lp_atom_eval_def)
qed

abbreviation lpp_ground_tree_goal where
 "lpp_ground_tree_goal p s \<equiv> (p,[lp_ieval (lpp_reify_structure s) LPIVar])"
abbreviation lpp_ground_spine_goal where
 "lpp_ground_spine_goal q ts \<equiv>
   (q,[lp_ieval (lpp_reified_spine (map lpp_reify_structure ts)) LPIVar])"

lemma lpp_ground_observation_spine_success:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 and calls: "list_all (\<lambda>s. \<forall>rest.
   ((lpp_ground_tree_goal p s#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) ts"
 shows "((lpp_ground_spine_goal q ts#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 using calls
proof (induct ts arbitrary: rest)
 case Nil show ?case using r_into_rtrancl[OF lpp_ground_observation_nil_step[OF core],of rest env] by simp
next
 case (Cons t ts)
 have first_step: "((lpp_ground_spine_goal q (t#ts)#rest,env),
   (lpp_ground_tree_goal p t#lpp_ground_spine_goal q ts#rest,env))\<in>lp_seg_answer_step P"
  using lpp_ground_observation_cons_step[OF core] by simp
 have head_path: "((lpp_ground_tree_goal p t#lpp_ground_spine_goal q ts#rest,env),
   (lpp_ground_spine_goal q ts#rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  using Cons.prems by simp
 have tail_path: "((lpp_ground_spine_goal q ts#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
  using Cons.hyps Cons.prems by simp
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF first_step] rtrancl_trans[OF head_path tail_path]])
qed

lemma lpp_ground_observation_success:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 and leaf_free: "lpp_no_variable_leaf s"
 shows "((lpp_ground_tree_goal p s#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 using leaf_free
proof (induct s arbitrary: rest)
 case (Var x) then show ?case by simp
next
 case (Fun f ts)
 obtain g where symbol: "f=Inl g" using Fun.prems by (cases f) auto
 have children: "list_all (\<lambda>s. \<forall>rest.
   ((lpp_ground_tree_goal p s#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*) ts"
  using Fun.hyps Fun.prems symbol by (auto simp: list_all_iff)
 have first_step: "((lpp_ground_tree_goal p (Fun f ts)#rest,env),
   (lpp_ground_spine_goal q ts#rest,env))\<in>lp_seg_answer_step P"
  using lpp_ground_observation_node_step[OF core] symbol by simp
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF first_step] lpp_ground_observation_spine_success[OF core children]])
qed

lemma lpp_ground_template_observation_success:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 and ground: "vars_term u = {}"
 shows "((lpp_ground_tree_goal p (lpp_structure_template u)#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 by (rule lpp_ground_observation_success[OF core lpp_ground_template_no_variable_leaf[OF ground]])

lemma lpp_ground_runtime_observation_leaf_free:
 assumes ground: "lp_seg_ground runtime_value"
 and observed: "lpp_runtime_structure runtime_value observed_tree"
 shows "lpp_no_variable_leaf observed_tree"
proof -
 obtain u where runtime: "runtime_value = lp_ieval u LPIVar"
  and shape: "observed_tree = lpp_structure_template u"
  using observed unfolding lpp_runtime_structure_def by blast
 have template_ground: "vars_term u = {}"
  using ground runtime by (auto simp: lp_seg_ground_eval elim: lp_seg_ground.cases)
 show ?thesis using lpp_ground_template_no_variable_leaf[OF template_ground] shape by simp
qed

lemma lpp_ground_runtime_observation_success:
 assumes core: "set (lpp_ground_observation_program p q) \<subseteq> set P"
 and ground: "lp_seg_ground runtime_value"
 and observed: "lpp_runtime_structure runtime_value observed_tree"
 shows "((lpp_ground_tree_goal p observed_tree#rest,env),(rest,env))\<in>(lp_seg_answer_step P)\<^sup>*"
 by (rule lpp_ground_observation_success[OF core lpp_ground_runtime_observation_leaf_free[OF ground observed]])

lemma lpp_ground_observation_rejects_leaf:
 assumes distinct: "p\<noteq>q"
 shows "\<not> (((p,[LPIFun LPPStructureLeaf []])#rest,env),next_state)
   \<in>lp_seg_answer_step (lpp_ground_observation_program p q)"
 using distinct
 by (cases next_state) (auto elim!: lp_seg_answer_step.cases
   simp: lpp_ground_observation_program_def lp_iatom_subst_def lp_atom_eval_def
   less_Suc_eq nth_Cons split: nat.splits)

ML \<open>
val checked = @{thms lpp_ground_observation_node_step lpp_ground_observation_nil_step
 lpp_ground_observation_cons_step lpp_ground_observation_spine_success
 lpp_ground_observation_success lpp_ground_template_observation_success lpp_ground_observation_rejects_leaf lpp_ground_runtime_observation_leaf_free lpp_ground_runtime_observation_success};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground observation program" else ();
\<close>
end
