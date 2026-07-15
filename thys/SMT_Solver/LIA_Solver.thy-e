theory LIA_Solver
  imports
    Ord.IA_Checker  
    LA_Solver_Common
begin

definition convert_lin_poly :: "String.literal lin_poly \<Rightarrow> (IA.sig, string \<times> IA.ty) Term.term" where
  "convert_lin_poly cxs = Fun (IA.SumF (length cxs))
     (map ( \<lambda> (c,x). Fun (IA.ProdF 2) [ 
        Fun (IA.ConstF (int_of_integer c)) [],
        Var (String.explode x, IA.IntT)]) cxs)"

fun convert_lin_rel :: "lin_rel \<Rightarrow> IA.sig" where
  "convert_lin_rel Less = IA.LessF" 
| "convert_lin_rel Less_Equal = IA.LeF" 
| "convert_lin_rel Equal = IA.EqF" 

fun convert_lin_constraint :: "String.literal lin_constraint \<Rightarrow> (IA.sig, string \<times> IA.ty) Term.term" where
  "convert_lin_constraint (Lin_Constraint p r c) = 
     Fun (convert_lin_rel r) [convert_lin_poly p, Fun (IA.ConstF (int_of_integer c)) []]" 

context IA_locale
begin

lemma convert_lin_poly[simp]: "convert_lin_poly p :\<^sub>f IntT" 
  apply (simp add: convert_lin_poly_def)
  apply (intro allI impI)
  subgoal for i by (cases "p ! i", simp add: Utility.all_less_two)
  done

lemma convert_lin_rel[simp]:
  "param_types (convert_lin_rel r) = [IntT, IntT]" 
  "return_type (convert_lin_rel r) = BoolT" 
  by (cases r, auto)+

lemma convert_lin_constraint: "is_bool (convert_lin_constraint f)" 
proof (cases f)
  case f: (Lin_Constraint p r c)
  show ?thesis unfolding f
    by (simp add: Utility.all_less_two)
qed
end

fun lia_validity_checker :: "String.literal lin_constraint formula \<Rightarrow> String.literal" where
  "lia_validity_checker f = (case 
     IA.check_valid_formula (LA_Solver BB_Solver) 
       (map_formula convert_lin_constraint f)
     of Inr _ \<Rightarrow> STR ''formula is valid''
      | Inl e \<Rightarrow> (showsl_lit (STR ''formula is perhaps not valid, answer of solver should contain counter-model\<newline>'') o e) (STR ''''))" 


value (code) "lia_validity_checker example_la_formula" 

export_code lia_validity_checker example_la_formula in Haskell
  module_name LIA_Checker file LIA_Checker


end