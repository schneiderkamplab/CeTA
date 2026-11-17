theory LP_Ranked_Representation
  imports LP_MGU_Representation Category_Properties.LP_Ranked_MGU_Properties
begin

text \<open>Native symbols carry their argument count at the semantic boundary.
Predicate and function occurrences are ranked independently, so overloaded names
remain distinct. The native program and serialized certificate are unchanged.\<close>
definition logic_rank_atom ::
  "('f,('f,'v) fo_term) logic_atom \<Rightarrow> ('f \<times> nat,('f \<times> nat,'v) fo_term) logic_atom" where
  "logic_rank_atom a = logic_tag_atom (logic_atom_map logic_rank_term a)"
definition logic_rank_program ::
  "('f,'v) logic_clause list \<Rightarrow> ('f \<times> nat,'v) logic_clause list" where
  "logic_rank_program P = map (\<lambda>(h,bs). (logic_rank_atom h,map logic_rank_atom bs)) P"

lemma logic_rank_term_correct[simp]: "arity_correct snd (logic_rank_term t)"
  by (induct t) (auto simp: list_all_iff simp del: correct_term_iff)
lemma logic_rank_atom_correct[simp]:
  "logic_atom_correct snd (arity_correct snd) (logic_rank_atom a)"
  by (cases a) (simp add: logic_rank_atom_def list_all_iff del: correct_term_iff)
lemma logic_rank_problem:
  "logic_problem snd (logic_rank_program P) (p,length modes) modes"
  by (auto simp: logic_problem_def logic_rank_program_def list_all_iff)
lemma logic_rank_atom_embed:
  "logic_atom_map logic_embed (logic_rank_atom a) =
    logic_rank_runtime_atom (logic_atom_map logic_embed a)"
  by (cases a) (simp add: logic_rank_atom_def logic_rank_runtime_atom_def map_map o_def logic_rank_embed)
lemma logic_rank_runtime_atom_subst:
  "logic_rank_runtime_atom (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (logic_rank_tree \<circ> s)) (logic_rank_runtime_atom a)"
  by (cases a) (simp add: logic_rank_runtime_atom_def map_map o_def logic_rank_subst)
lemma logic_rank_atom_eval:
  "logic_atom_map (logic_eval (logic_rank_tree \<circ> s)) (logic_rank_atom a) =
    logic_rank_runtime_atom (logic_atom_map (logic_eval s) a)"
  by (cases a) (simp add: logic_rank_atom_def logic_rank_runtime_atom_def
    map_map o_def logic_rank_subst logic_rank_embed[symmetric])
lemma logic_rank_ground[simp]: "logic_ground (logic_rank_term t) = logic_ground t"
  by (induct t) (auto simp: list_all_iff)
lemma logic_rank_query:
  assumes len: "length (logic_arguments a) = length modes"
    and pred: "logic_predicate a = p"
    and gr: "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t) (zip (logic_arguments a) modes)"
  shows "logic_query snd (p,length modes) modes (logic_rank_atom a)"
  using assms by (cases a)
    (simp add: logic_query_def logic_rank_atom_def zip_map1 o_def split_def
      list_all_iff del: correct_term_iff)

lemma logic_variables_variable[simp]: "logic_variables (LVar x) = {x}"
  by (auto simp: logic_variables_def dest: logic_subtree_variable intro: logic_subtree.root)
lemma logic_variables_function[simp]:
  "logic_variables (LFun f ts) = \<Union>(logic_variables ` set ts)"
  by (auto simp: logic_variables_def logic_subtree_function)
lemma logic_rank_finite_variables:
  "logic_variables (logic_embed (logic_rank_term (from_term t))) = vars_term t"
  by (induct t) auto
lemma logic_finite_variables:
  "logic_variables (logic_embed (from_term t)) = vars_term t"
  by (induct t) auto

end
