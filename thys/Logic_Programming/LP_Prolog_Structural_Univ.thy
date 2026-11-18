theory LP_Prolog_Structural_Univ
 imports LP_Prolog_Structural_Projection
begin

fun lpp_structural_argument_list ::
 "((string lp_cut_symbol + unit,unit) term) list \<Rightarrow> (string lp_cut_symbol + unit,unit) term" where
 "lpp_structural_argument_list [] = Fun (Inl (LPCUser ''0:prolog_data_5b5d'')) []"
| "lpp_structural_argument_list (t#ts) = Fun (Inl (LPCUser ''2:prolog_data_2e'')) [t,lpp_structural_argument_list ts]"

fun lpp_structural_univ ::
 "(string lp_cut_symbol + unit,unit) term \<Rightarrow> string lp_cut_symbol \<Rightarrow>
  (string lp_cut_symbol + unit,unit) term \<Rightarrow> bool" where
 "lpp_structural_univ (Var x) f argument_shape = False"
| "lpp_structural_univ (Fun (Inr u) ts) f argument_shape = False"
| "lpp_structural_univ (Fun (Inl g) ts) f argument_shape = (g=f \<and> argument_shape=lpp_structural_argument_list ts)"

lemma lpp_structural_argument_list_observed:
 "lpp_runtime_structure (lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) children))
   (lpp_structural_argument_list (map lpp_structure_template children))"
proof (induction children)
 case Nil
 show ?case unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Fun (LPCUser ''0:prolog_data_5b5d'') []"]) simp
next
 case (Cons t ts)
 obtain tail_template where tail:
  "lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) ts)=lp_ieval tail_template LPIVar"
 and shape: "lpp_structural_argument_list (map lpp_structure_template ts)=lpp_structure_template tail_template"
  using Cons.IH unfolding lpp_runtime_structure_def by blast
 show ?case unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Fun (LPCUser ''2:prolog_data_2e'') [t,tail_template]"])
   (simp add: tail shape)
qed

lemma lpp_constructor_arguments_structural_univ:
 assumes actual: "lpp_constructor_arguments value f arguments"
 and node: "lpp_runtime_structure value node_structure"
 and argument_shape: "lpp_runtime_structure arguments arguments_structure"
 shows "lpp_structural_univ node_structure f arguments_structure"
proof -
 have finite: "lpp_finite_term value" by (rule lpp_runtime_structure_finite[OF node])
 obtain children where represented: "value=lp_ieval (Fun f children) LPIVar"
 and arguments: "arguments=lpp_argument_list (map (\<lambda>t. lp_ieval t LPIVar) children)"
  using lpp_constructor_arguments_finite_template[OF actual finite] by blast
 have observed_node: "lpp_runtime_structure value (Fun (Inl f) (map lpp_structure_template children))"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "Fun f children"]) (simp add: represented)
 have observed_args: "lpp_runtime_structure arguments (lpp_structural_argument_list (map lpp_structure_template children))"
  unfolding arguments by (rule lpp_structural_argument_list_observed)
 show ?thesis using lpp_runtime_structure_unique[OF node observed_node]
  lpp_runtime_structure_unique[OF argument_shape observed_args] by simp
qed

lemma lpp_structural_univ_rejects_variable_leaf:
 "\<not>lpp_structural_univ (lpp_structure_template (Var x)) f argument_shape"
 by simp

ML \<open>
val checked = @{thms lpp_structural_argument_list_observed lpp_constructor_arguments_structural_univ
 lpp_structural_univ_rejects_variable_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted structural univ" else ();
\<close>
end
