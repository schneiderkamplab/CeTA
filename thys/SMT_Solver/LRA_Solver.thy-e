theory LRA_Solver
  imports
    RA_Checker  
    Show.Shows_Literal
    Containers.Containers
    "HOL-Library.Code_Abstract_Char" 
    "HOL-Library.Code_Target_Numeral" 
begin

fun to_rat :: "integer \<Rightarrow> rat" where
  "to_rat x = Rat.Fract (int_of_integer x) 1" 

definition convert_lin_poly :: "String.literal lin_poly \<Rightarrow> (RA.sig, string \<times> RA.ty) Term.term" where
  "convert_lin_poly cxs = Fun (RA.SumF (length cxs))
     (map ( \<lambda> (r,x). Fun (RA.ProdF 2) [ 
        Fun (RA.ConstF (to_rat r)) [],
        Var (String.explode x, RA.RatT)]) cxs)"

fun convert_lin_rel :: "lin_rel \<Rightarrow> RA.sig" where
  "convert_lin_rel Less = RA.LessF" 
| "convert_lin_rel Less_Equal = RA.LeF" 
| "convert_lin_rel Equal = RA.EqF" 

fun convert_lin_constraint :: "String.literal lin_constraint \<Rightarrow> (RA.sig, string \<times> RA.ty) Term.term" where
  "convert_lin_constraint (Lin_Constraint p r c) = 
     Fun (convert_lin_rel r) [convert_lin_poly p, Fun (RA.ConstF (to_rat c)) []]" 

context RA_locale
begin

lemma convert_lin_poly[simp]: "convert_lin_poly p :\<^sub>f RatT" 
  apply (simp add: convert_lin_poly_def)
  apply (intro allI impI)
  subgoal for i by (cases "p ! i", simp add: Utility.all_less_two)
  done

lemma convert_lin_rel[simp]:
  "param_types (convert_lin_rel r) = [RatT, RatT]" 
  "return_type (convert_lin_rel r) = BoolT" 
  by (cases r, auto)+

lemma convert_lin_constraint: "is_bool (convert_lin_constraint f)" 
proof (cases f)
  case f: (Lin_Constraint p r c)
  show ?thesis unfolding f
    by (simp add: Utility.all_less_two)
qed
end

fun lra_validity_checker :: "String.literal lin_constraint formula \<Rightarrow> String.literal" where
  "lra_validity_checker f = (case 
     RA.check_valid_formula (LA_Solver Simplex_Solver) 
       (map_formula convert_lin_constraint f)
     of Inr _ \<Rightarrow> STR ''formula is valid''
      | Inl e \<Rightarrow> (showsl_lit (STR ''formula is perhaps not valid, answer of solver should contain counter-model\<newline>'') o e) (STR ''''))" 


value (code) "lra_validity_checker example_la_formula" 

export_code lra_validity_checker example_la_formula in Haskell
  module_name LRA_Checker file LRA_Checker


end