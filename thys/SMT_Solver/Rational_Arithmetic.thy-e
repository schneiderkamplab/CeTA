(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Rational_Arithmetic
imports
  Ord.Formula
  Deriving.Compare_Generator
  Certification_Monads.Check_Monad
  Ord.Non_Inf_Orders
  Ord.Show_Literal_Polynomial  
  LA_Solver_Common
begin

locale RA_locale
begin

datatype ty = BoolT | RatT

datatype sig = LessF | LeF | SumF nat | ConstF (the_ConstF: rat) | ProdF nat | EqF

datatype "val" = Rat (to_rat: rat) | Bool (to_bool: bool)

type_synonym 'v exp = "(sig,'v,ty) Sorted_Algebra.exp"

type_synonym 'v formula = "'v exp Formula.formula"

abbreviation "var x \<equiv> Var (x,RatT)"
abbreviation le_t where "le_t s t \<equiv> Atom (Fun LeF [s,t])"
abbreviation less_t where "less_t s t \<equiv> Atom (Fun LessF [s,t])"
abbreviation eq_t where "eq_t s t \<equiv> Atom (Fun EqF [s,t])"

fun type_of_fun :: "sig \<Rightarrow> ty list \<times> ty" where
  "type_of_fun LessF = ([RatT,RatT], BoolT)"
| "type_of_fun LeF = ([RatT,RatT], BoolT)"
| "type_of_fun EqF = ([RatT,RatT], BoolT)"
| "type_of_fun (SumF n) = (replicate n RatT, RatT)"
| "type_of_fun (ConstF _) = ([], RatT)"
| "type_of_fun (ProdF n) = (replicate n RatT, RatT)" 

fun Values_of_type :: "ty \<Rightarrow> val set" where
  "Values_of_type BoolT = range Bool"
| "Values_of_type RatT = range Rat"

lemma mem_Values_of_typeE[elim]:
  assumes "v \<in> Values_of_type ty"
      and "\<And>i. ty = RatT \<Longrightarrow> v = Rat i \<Longrightarrow> thesis"
      and "\<And>b. ty = BoolT \<Longrightarrow> v = Bool b \<Longrightarrow> thesis"
  shows "thesis" using assms by (cases ty, auto)

lemma mem_Values_of_typeD[dest]:
  assumes "v \<in> Values_of_type ty"
  shows "(ty = RatT \<longrightarrow> (\<exists>i. v = Rat i)) \<and> (ty = BoolT \<longrightarrow> (\<exists>b. v = Bool b))"
  by (insert assms, auto)

fun "I" :: "sig \<Rightarrow> val list \<Rightarrow> val" where
  "I LessF [x, y] = Bool (to_rat x < to_rat y)"
| "I LeF [x, y] = Bool (to_rat x \<le> to_rat y)"
| "I EqF [x, y] = Bool (to_rat x = to_rat y)"
| "I (SumF n) xs = Rat (sum_list (map to_rat xs))"
| "I (ConstF x) [] = Rat x"
| "I (ProdF n) xs = Rat (prod_list (map to_rat xs))"
| "I _ _ = undefined"

sublocale prelogic
  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and type_fixer= "TYPE(_)".

abbreviation const where "const x \<equiv> Fun (ConstF x) []"

end

(* don't do this before "sublocale prelogic"; otherwise you lose term RA.eval *)
global_interpretation RA: RA_locale.

notation RA.le_t (infix "\<le>\<^sub>R\<^sub>A" 50)
notation RA.less_t (infix "<\<^sub>R\<^sub>A" 50)
notation RA.eq_t (infix "=\<^sub>R\<^sub>A" 50)
notation RA.valid ("\<Turnstile>\<^sub>R\<^sub>A _" [40]40)


instantiation RA.sig :: showl
begin
fun showsl_sig where 
  "showsl_sig RA.LessF = showsl_lit (STR ''<'')" 
| "showsl_sig RA.LeF = showsl_lit (STR ''<='')" 
| "showsl_sig RA.EqF = showsl_lit (STR ''='')" 
| "showsl_sig (RA.SumF n) = showsl_lit (STR ''+'')" 
| "showsl_sig (RA.ProdF n) = showsl_lit (STR ''*'')" 
| "showsl_sig (RA.ConstF n) = showsl n" 
definition "showsl_list (xs :: RA.sig list) = default_showsl_list showsl xs"
instance ..
end

instantiation RA.ty :: showl
begin
fun showsl_ty where 
  "showsl_ty RA.BoolT = showsl_lit (STR ''Bool'')" 
| "showsl_ty RA.RatT = showsl_lit (STR ''Rat'')" 
definition "showsl_list (xs :: RA.ty list) = default_showsl_list showsl xs"
instance ..
end

derive compare_order RA.val

context RA_locale
begin

lemma has_type_induct[consumes 1, case_names Less Lesseq Equals Sum Const Prod Var]:
  assumes "e :\<^sub>f ty"
  and LessCase: "\<And> ta tb.
       ta :\<^sub>f RatT \<Longrightarrow> tb :\<^sub>f RatT \<Longrightarrow> P ta RatT \<Longrightarrow> P tb RatT \<Longrightarrow> P (Fun RA.LessF [ta,tb]) BoolT"
  and LesseqCase: "\<And> ta tb.
       ta :\<^sub>f RatT \<Longrightarrow> tb :\<^sub>f RatT \<Longrightarrow> P ta RatT \<Longrightarrow> P tb RatT \<Longrightarrow> P (Fun RA.LeF [ta,tb]) BoolT"
  and EqualsCase: "\<And> ta tb.
       ta :\<^sub>f RatT \<Longrightarrow> tb :\<^sub>f RatT \<Longrightarrow> P ta RatT \<Longrightarrow> P tb RatT \<Longrightarrow> P (Fun RA.EqF [ta,tb]) BoolT"
  and SumCase: "\<And> ts n.
       (\<And> t. t \<in> set ts \<Longrightarrow> t :\<^sub>f RatT) \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> P t RatT) \<Longrightarrow> P (Fun (SumF n) ts) RatT"
  and ConstCase: "\<And> x. P (const x) RatT"
  and ProdCase: "\<And> ts n. 
       (\<And> t. t \<in> set ts \<Longrightarrow> t :\<^sub>f RatT) \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> P t RatT) \<Longrightarrow> P (Fun (ProdF n) ts) RatT"
  and VarCase: "\<And> x ty. P (Var (x,ty)) ty"
  shows "P e ty"
using assms(1) proof(induct e ty rule: has_type.induct)
  case (1 x ty) with VarCase show ?case by(cases x, auto)
next
  case Fun: (2 f ls ty)
  show ?case
  proof(cases f)
    case [simp]: LessF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f RatT" and bt: "tb :\<^sub>f RatT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] LessCase show ?thesis by auto
  next
    case [simp]: LeF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f RatT" and bt: "tb :\<^sub>f RatT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] LesseqCase show ?thesis by auto
  next
    case [simp]: EqF
    from Fun(2) obtain ta tb where [simp]: "ls = [ta,tb]" by (cases ls rule: list_3_cases, auto)
    from Fun(2) have at: "ta :\<^sub>f RatT" and bt: "tb :\<^sub>f RatT" and ty: "ty = BoolT" by auto
    with Fun.hyps[of 0] Fun.hyps[of 1] EqualsCase show ?thesis by auto
  next
    case [simp]: (SumF n)
    {
      fix l
      assume "l \<in> set ls" 
      then obtain i where l: "l = ls ! i" and i: "i < length ls" unfolding set_conv_nth by auto
      from Fun(2) l i have lty: "l :\<^sub>f RatT" by auto
      from Fun.hyps[OF i] lty i l Fun(2) have "P l RatT" by auto
      note lty this
    }
    from SumCase[OF this, of ls n] Fun(2) show ?thesis by auto
  next
    case [simp]: (ConstF x)
    with Fun have [simp]: "ls = []" by auto
    show ?thesis using Fun ConstCase by simp
  next
    case [simp]: (ProdF n)
    {
      fix l
      assume "l \<in> set ls" 
      then obtain i where l: "l = ls ! i" and i: "i < length ls" unfolding set_conv_nth by auto
      from Fun(2) l i have lty: "l :\<^sub>f RatT" by auto
      from Fun.hyps[OF i] lty i l Fun(2) have "P l RatT" by auto
      note lty this
    }
    from ProdCase[OF this, of ls n] Fun(2) show ?thesis by auto
  qed
qed

sublocale logic
  where I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and type_fixer = "TYPE(_)"
proof
  fix f ds
  show "length ds = length (param_types f) \<Longrightarrow>
       (\<And>i. i < length ds \<Longrightarrow> ds ! i \<in> Values_of_type (param_types f ! i)) \<Longrightarrow>
       I f ds \<in> Values_of_type (return_type f)"
  by (cases f; induct f ds rule: RA.I.induct, auto)
  show "Values_of_type ty \<noteq> {}" for ty by(cases ty, auto)
qed

lemmas [simp] = less_val_def compare_val_def lt_of_comp_def comparator_of_def

lemma less_RA_value_simps[simp]:
 "\<And>x y. Bool x > Bool y \<longleftrightarrow> x > y"
 "\<And>x y. Bool x > Rat y"
 "\<And>x y. Rat x > Rat y \<longleftrightarrow> x > y"
 "\<And>x y. Rat x > Bool y \<longleftrightarrow> False"
proof-
  show "Bool x > Bool y \<longleftrightarrow> x > y" for x y by (cases x; cases y, auto)
qed auto

lemmas [simp del] = less_val_def compare_val_def lt_of_comp_def comparator_of_def

lemma val_le[simp]: "(x :: val) \<ge> y \<longleftrightarrow> x = y \<or> x > y" by auto

lemma to_rat_iff:
  assumes \<alpha>: "assignment \<alpha>" and s: "s :\<^sub>f RatT" and t: "t :\<^sub>f RatT"
  shows "to_rat (\<lbrakk>s\<rbrakk>\<alpha>) < to_rat (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> < \<lbrakk>t\<rbrakk>\<alpha>"
    and "to_rat (\<lbrakk>s\<rbrakk>\<alpha>) \<le> to_rat (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> \<le> \<lbrakk>t\<rbrakk>\<alpha>"
    and "to_rat (\<lbrakk>s\<rbrakk>\<alpha>) = to_rat (\<lbrakk>t\<rbrakk>\<alpha>) \<longleftrightarrow> \<lbrakk>s\<rbrakk>\<alpha> = \<lbrakk>t\<rbrakk>\<alpha>"
  using s t by (auto dest!: eval_types[OF \<alpha>])

end

subsection \<open>Non-term, polynomial version\<close>

type_synonym 'v rpoly = "('v,rat)poly" 

context
  notes [[typedef_overloaded]]
begin
datatype 'v poly_constraint = 
  Poly_Ge "'v rpoly" (* meaning: p \<ge> 0 *)
| Poly_Gt "'v rpoly" (* meaning: p > 0 *)
| Poly_Eq "'v rpoly" (* meaning: p = 0 *) 
end

context RA_locale begin

fun showsl_poly_constraint :: "'v :: {showl,linorder} poly_constraint \<Rightarrow> showsl" where 
  "showsl_poly_constraint (Poly_Ge p) = (showsl_poly p o showsl_lit (STR '' >= 0''))"
| "showsl_poly_constraint (Poly_Gt p) = (showsl_poly p o showsl_lit (STR '' > 0''))"
| "showsl_poly_constraint (Poly_Eq p) = (showsl_poly p o showsl_lit (STR '' = 0''))"

fun interpret_poly_constraint :: "('v :: linorder \<Rightarrow> rat) \<Rightarrow> 'v poly_constraint \<Rightarrow> bool" where
  "interpret_poly_constraint f (Poly_Ge p) = (eval_poly f p \<ge> 0)" 
| "interpret_poly_constraint f (Poly_Gt p) = (eval_poly f p > 0)" 
| "interpret_poly_constraint f (Poly_Eq p) = (eval_poly f p = 0)" 
  
fun vars_poly_constraint :: "'v :: linorder poly_constraint \<Rightarrow> 'v set" where
  "vars_poly_constraint (Poly_Ge p) = poly_vars p"
| "vars_poly_constraint (Poly_Gt p) = poly_vars p"
| "vars_poly_constraint (Poly_Eq p) = poly_vars p"

fun vars_poly_constraint_list :: "'v :: linorder poly_constraint \<Rightarrow> 'v list" where
  "vars_poly_constraint_list (Poly_Ge p) = poly_vars_list p"
| "vars_poly_constraint_list (Poly_Gt p) = poly_vars_list p"
| "vars_poly_constraint_list (Poly_Eq p) = poly_vars_list p"
  
lemma vars_poly_constraint_list[simp]: "set (vars_poly_constraint_list c) = vars_poly_constraint c" 
  by (cases c, auto)

fun RA_exp_to_tpoly :: "'v RA.exp \<Rightarrow> ('v,rat) tpoly" where
 "RA_exp_to_tpoly (Var (a,ty)) = PVar a" |
 "RA_exp_to_tpoly (Fun (SumF _) as) = PSum (map RA_exp_to_tpoly as)" |
 "RA_exp_to_tpoly (Fun (ConstF a) []) = PNum a" |
 "RA_exp_to_tpoly (Fun (ProdF _) as) = PMult (map RA_exp_to_tpoly as)"
    
definition RA_exp_to_poly :: "'v :: linorder RA.exp \<Rightarrow> ('v,rat) poly" where
  "RA_exp_to_poly = poly_of o RA_exp_to_tpoly" 

fun RA_exp_to_poly_constraint :: "'v :: linorder RA.exp \<Rightarrow> 'v poly_constraint" where
  "RA_exp_to_poly_constraint (Fun LeF [a, b]) = Poly_Ge (poly_minus (RA_exp_to_poly b) (RA_exp_to_poly a))" 
| "RA_exp_to_poly_constraint (Fun EqF [a, b]) = Poly_Eq (poly_minus (RA_exp_to_poly b) (RA_exp_to_poly a))" 
| "RA_exp_to_poly_constraint (Fun LessF [a, b]) = Poly_Gt (poly_minus (RA_exp_to_poly b) (RA_exp_to_poly a))" 

lemma RA_exp_to_tpoly:
  assumes \<alpha>: "assignment \<alpha>"
  and "e :\<^sub>f RatT"
  shows "\<lbrakk>e\<rbrakk>\<alpha> = Rat (eval_tpoly (\<lambda>a. to_rat (\<alpha> (a, RatT))) (RA_exp_to_tpoly e))"
proof -
  have "e :\<^sub>f RatT \<Longrightarrow> ?thesis" 
  proof(induct e RatT rule:has_type_induct)
    case (Var x)
    from \<alpha> obtain i where "\<alpha> (x, RatT) = Rat i" by force
    then show ?case by auto
  next
    case (Sum es n)
    then show ?case by (auto, induct es, auto)
  next
    case (Prod es n)
    then show ?case by (auto, induct es, auto)
  qed auto
  then show ?thesis using assms by simp
qed
  
lemma RA_exp_to_poly:
  assumes \<alpha>: "assignment \<alpha>"
  and "e :\<^sub>f RatT"
shows "\<lbrakk>e\<rbrakk>\<alpha> = Rat (eval_poly (\<lambda>a. to_rat (\<alpha> (a, RatT))) (RA_exp_to_poly e))"
  using RA_exp_to_tpoly[OF assms] unfolding RA_exp_to_poly_def o_def poly_of .
  
lemma RA_exp_to_poly_constraint: 
  assumes \<alpha>: "assignment \<alpha>"
  and e: "is_bool e"
  shows "to_bool (\<lbrakk>e\<rbrakk>\<alpha>) = (interpret_poly_constraint (\<lambda>a. to_rat (\<alpha> (a, RatT))) (RA_exp_to_poly_constraint e))"
proof -
  have "e :\<^sub>f BoolT \<Longrightarrow> is_Fun e \<Longrightarrow> ?thesis"
    by (induct e BoolT rule: has_type_induct, insert RA_exp_to_poly[OF \<alpha>], auto)
  then show ?thesis using e[unfolded is_bool_def] by auto
qed

fun showsl_RA_exp where
  "showsl_RA_exp (Fun LessF [s,t]) = showsl_RA_exp s o showsl_lit (STR '' < '') o showsl_RA_exp t"
| "showsl_RA_exp (Fun LeF [s,t]) = showsl_RA_exp s o showsl_lit (STR '' <= '') o showsl_RA_exp t"
| "showsl_RA_exp (Fun EqF [s,t]) = showsl_RA_exp s o showsl_lit (STR '' = '') o showsl_RA_exp t"
| "showsl_RA_exp e = showsl_poly (RA_exp_to_poly e)"

definition "showsl_RA_clause = showsl_list_gen showsl_RA_exp (STR ''FALSE'') (STR '''') (STR '' || '') (STR '''')" 

definition "showsl_RA_formula = showsl_list_gen (showsl_paren o showsl_RA_clause) (STR ''TRUE'') (STR '''') (STR '' && '') (STR '''')" 

end

end
