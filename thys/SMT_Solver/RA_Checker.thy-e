(*
Author:  Sebastiaan Joosten (2016-2017)
Author:  René Thiemann (2016-2017)
Author:  Akihisa Yamada (2016-2017)
License: LGPL (see file COPYING.LESSER)
*)
theory RA_Checker
imports
  Rational_Arithmetic
  Ord.Branch_and_Bound
  "HOL-Library.Mapping"
begin

no_notation Simplex.curr_val_satisfies_state ("\<Turnstile>")
hide_const (open) eval_poly

datatype la_solver_type = Simplex_Solver 

fun la_solver :: "la_solver_type \<Rightarrow> constraint list \<Rightarrow> (nat \<Rightarrow> rat) option" where
  "la_solver Simplex_Solver cs = (case simplex cs of Unsat _ \<Rightarrow> None | Sat v \<Rightarrow> Some (\<lambda> x. (\<langle>v\<rangle> x)))" 

lemma la_solver_unsat: assumes "la_solver type cs = None"
  shows "\<not> v \<Turnstile>\<^sub>c\<^sub>s set cs"
proof (cases type)
  case Simplex_Solver
  thus ?thesis using simplex(1)[of cs] assms by (auto split: sum.splits)
qed

subsection \<open>Validity checking functionality\<close>

datatype 'v linearity = Non_Linear | One | Variable 'v

fun monom_list_linearity :: "'v monom_list \<Rightarrow> 'v linearity" where
  "monom_list_linearity [] = One"
| "monom_list_linearity [(x,n)] = (if n = 1 then Variable x else Non_Linear)"
| "monom_list_linearity _ = Non_Linear"

lift_definition monom_linearity :: "'v :: linorder monom \<Rightarrow> 'v linearity" is monom_list_linearity .

lemma monom_linearity: "monom_linearity m = One \<Longrightarrow> eval_monom \<alpha> m = 1"
  "monom_linearity (m :: 'v :: linorder monom) = Variable x \<Longrightarrow> eval_monom \<alpha> m = \<alpha> x"
  "monom_linearity (m :: 'v :: linorder monom) = Variable x \<Longrightarrow> monom_vars_list m = [x]"
proof (atomize (full), transfer fixing: x \<alpha>)
  fix m :: "'v monom_list"
  show "(monom_list_linearity m = linearity.One \<longrightarrow> eval_monom_list \<alpha> m = 1) \<and>
         (monom_list_linearity m = Variable x \<longrightarrow> eval_monom_list \<alpha> m = \<alpha> x) \<and>
         (monom_list_linearity m = Variable x \<longrightarrow> map fst m = [x])"
    by (cases m, force, cases "tl m", cases "hd m", auto)
qed

context RA_locale begin

subsubsection \<open>Via Automatic Solver\<close>

context
  fixes \<rho> :: "'v :: linorder \<Rightarrow> nat" (* renamings between variables *)
    and \<tau> :: "nat \<Rightarrow> 'v"
begin
fun rpoly_to_linear_poly :: "'v rpoly \<Rightarrow> (linear_poly \<times> rat) option" where
  "rpoly_to_linear_poly [] = Some (0,0)"
| "rpoly_to_linear_poly ((monomial,c) # rest) = do {
     (p,d) \<leftarrow> rpoly_to_linear_poly rest;
     case monom_linearity monomial of
       One \<Rightarrow> Some (p,c + d)
     | Variable x \<Rightarrow> Some (lp_monom (of_rat c) (\<rho> x) + p, d)
     | Non_Linear \<Rightarrow> None
  }"

definition True_constraint :: constraint where "True_constraint = GEQ 0 0"

lemma True_constraint[simp]: "a \<Turnstile>\<^sub>c True_constraint"
  unfolding True_constraint_def by (auto, transfer, auto)

primrec to_linear_constraints :: "'v poly_constraint \<Rightarrow> constraint list" where
  "to_linear_constraints (Poly_Ge p) = (case rpoly_to_linear_poly p of None \<Rightarrow> []
       | Some (q,c) \<Rightarrow> [GEQ q (of_rat (- c))])"
| "to_linear_constraints (Poly_Gt p) = (case rpoly_to_linear_poly p of None \<Rightarrow> []
       | Some (q,c) \<Rightarrow> [GT q (of_rat (- c))])"
| "to_linear_constraints (Poly_Eq p) = (case rpoly_to_linear_poly p of None \<Rightarrow> []
       | Some (q,c) \<Rightarrow> [EQ q (of_rat (- c))])"

definition to_rat_assignment :: "('v \<Rightarrow> rat) \<Rightarrow> (nat \<Rightarrow> rat)" where
  "to_rat_assignment \<alpha> = (\<lambda> n. \<alpha> (\<tau> n))"

context
  fixes \<alpha> :: "'v :: linorder \<Rightarrow> rat"
    and \<beta> :: "nat \<Rightarrow> rat"
  assumes beta: "\<beta> = to_rat_assignment \<alpha>"
begin

lemma rpoly_to_linear_poly: "(\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v)
  \<Longrightarrow> rpoly_to_linear_poly p = Some (q, c)
  \<Longrightarrow> of_rat (eval_poly \<alpha> p) =  (q \<lbrace>\<beta>\<rbrace> + of_rat c)"
proof (induct p arbitrary: q c)
  case Nil
  then show ?case by (simp add: valuate_zero)
next
  case (Cons xc p qq e)
  obtain xs c where xc: "xc = (xs,c)" by force
  from Cons(3) xc obtain q d where p: "rpoly_to_linear_poly p = Some (q,d)" by (auto split: bind_splits)
  from Cons(1)[OF Cons(2) this] have IH: "of_rat (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_rat d" by (auto simp: poly_vars_def)
  show ?case
  proof (cases "monom_linearity xs")
    case One
    with Cons(3) p xc have id: "qq = q" "e = d + c" by auto
    show ?thesis unfolding id xc One using IH monom_linearity(1)[OF One] by auto
  next
    case (Variable x)
    note xs = monom_linearity(2-3)[OF Variable]
    from Cons(3) p xc Variable have id: "qq = lp_monom c (\<rho> x) + q" "e = d" by auto
    from Cons(2)[of x] have "\<tau> (\<rho> x) = x" unfolding xc poly_vars_def by (auto simp: xs)
    then show ?thesis unfolding id xc using IH xs(1)[of \<alpha>]
      by (simp add: Cons xc valuate_add valuate_lp_monom beta to_rat_assignment_def[abs_def] o_def ac_simps)
  qed (insert Cons, auto simp: xc split: bind_splits)
qed

lemma to_linear_constraints:
  assumes "interpret_poly_constraint \<alpha> c"
    and "(\<And> v. v \<in> vars_poly_constraint c \<Longrightarrow> \<tau> (\<rho> v) = v)"
    and cc: "cc \<in> set (to_linear_constraints c)"
  shows "\<beta> \<Turnstile>\<^sub>c cc"
proof (cases c)
  case (Poly_Ge p)
  let ?c = "rpoly_to_linear_poly p"
  show ?thesis
  proof (cases ?c)
    case (Some qc)
    then obtain q d where c: "?c = Some (q,d)" by (cases qc, auto)
    with Poly_Ge cc have id: "cc = GEQ q (of_rat (- d))" by auto
    from Poly_Ge assms(2) have "\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v" by auto
    from rpoly_to_linear_poly[OF this c]
    have id': "of_rat (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_rat d" by auto
    from assms(1)[unfolded Poly_Ge, simplified] have ge: "eval_poly \<alpha> p \<ge> 0" by auto
    show ?thesis unfolding id using ge id' by auto
  qed (insert Poly_Ge cc, auto)
next
  case (Poly_Gt p)
  let ?c = "rpoly_to_linear_poly p"
  show ?thesis
  proof (cases ?c)
    case (Some qc)
    then obtain q d where c: "?c = Some (q,d)" by (cases qc, auto)
    with Poly_Gt cc have id: "cc = GT q (of_rat (- d))" by auto
    from Poly_Gt assms(2) have "\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v" by auto
    from rpoly_to_linear_poly[OF this c]
    have id': "of_rat (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_rat d" by auto
    from assms(1)[unfolded Poly_Gt, simplified] have gt: "eval_poly \<alpha> p > 0" by auto
    show ?thesis unfolding id using gt id' by auto
  qed (insert Poly_Gt cc, auto)
next
  case (Poly_Eq p)
  let ?c = "rpoly_to_linear_poly p"
  show ?thesis
  proof (cases ?c)
    case (Some qc)
    then obtain q d where c: "?c = Some (q,d)" by (cases qc, auto)
    with Poly_Eq cc have id: "cc = EQ q (of_rat (- d))" by auto
    from Poly_Eq assms(2) have "\<And> v. v \<in> poly_vars p \<Longrightarrow> \<tau> (\<rho> v) = v" by auto
    from rpoly_to_linear_poly[OF this c]
    have id': "of_rat (eval_poly \<alpha> p) = q \<lbrace> \<beta> \<rbrace> + of_rat d" by auto
    from assms(1)[unfolded Poly_Eq, simplified] have eq: "eval_poly \<alpha> p = 0" by auto
    show ?thesis unfolding id using eq id' by auto
  qed (insert Poly_Eq cc, auto)
qed

lemma la_solver_to_linear_constraints_unsat:
  assumes "la_solver type (concat (map to_linear_constraints \<phi>s)) = None"
    and "\<And> \<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
    and renaming: "(\<And> v \<phi>. v \<in> vars_poly_constraint \<phi> \<Longrightarrow> \<phi> \<in> set \<phi>s \<Longrightarrow> \<tau> (\<rho> v) = v)"
  shows False
proof -
  from to_linear_constraints[OF assms(2) renaming]
  have "\<And> \<phi> c. \<phi> \<in> set \<phi>s \<Longrightarrow> c \<in> set (to_linear_constraints \<phi>) \<Longrightarrow> \<beta> \<Turnstile>\<^sub>c c" by auto
  then have "\<beta> \<Turnstile>\<^sub>c\<^sub>s set (concat (map to_linear_constraints \<phi>s))" by simp
  with la_solver_unsat[OF assms(1)]
  have "\<beta> \<noteq> v" for v by auto
  thus False unfolding beta to_rat_assignment_def by auto
qed
end
end

(* la_solver is not a decision procedure because of the linearization process;
   therefore if la_solver finds a solution, we always check it against the original constraints *)
definition unsat_via_la_solver :: "la_solver_type \<Rightarrow> 'v :: linorder poly_constraint list \<Rightarrow> ('v list \<times> ('v \<Rightarrow> rat)) option option" where
  "unsat_via_la_solver type les = (let vs = remdups (concat (map vars_poly_constraint_list les));
     ren_map = Mapping.of_alist (zip vs [0 ..< length vs]);
     ren_fun = (\<lambda> v. case Mapping.lookup ren_map v of None \<Rightarrow> 0 | Some n \<Rightarrow> n);
     cs = concat (map (to_linear_constraints ren_fun) les)     
    in case la_solver type cs of None \<Rightarrow> Some None  \<comment> \<open>unsat\<close>
     | Some \<beta> \<Rightarrow> \<comment> \<open>linearized constraints are sat\<close>
      let \<alpha> = \<beta> o ren_fun in if 
      (\<forall> li \<in> set les. interpret_poly_constraint \<alpha> li) then Some (Some (vs, \<alpha>)) else None)"

lemma sat_via_la_solver: assumes "unsat_via_la_solver type les = Some (Some (vs, \<alpha>))" 
  shows "\<phi> \<in> set les \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
  using assms unfolding unsat_via_la_solver_def Let_def
  by (auto split: option.splits if_splits)

lemma unsat_via_la_solver: assumes unsat: "unsat_via_la_solver type les = Some None"
  and sat: "\<And> \<phi>. \<phi> \<in> set les \<Longrightarrow> interpret_poly_constraint \<alpha> \<phi>"
shows False
proof -
  obtain vs ren_fun invi where
    vs: "vs = remdups (concat (map vars_poly_constraint_list les))" and
    ren_fun: "ren_fun = (\<lambda> v. case map_of (zip vs [0 ..< length vs]) v of None \<Rightarrow> 0 | Some n \<Rightarrow> n)" and
    inv: "invi = (\<lambda> i. vs ! i)" by auto
  have dist: "distinct vs" unfolding vs by auto
  {
    fix v \<phi>
    assume "v \<in> vars_poly_constraint \<phi>" "\<phi> \<in> set les"
    then have "v \<in> set vs" unfolding vs by auto
    then obtain i where i: "i < length vs" and v: "v = vs ! i" unfolding set_conv_nth by auto
    then have "ren_fun (vs ! i) = i" unfolding ren_fun using dist by simp
    then have "invi (ren_fun v) = v" unfolding v inv by simp
  } note inv = this
  from unsat[unfolded unsat_via_la_solver_def Let_def lookup_of_alist, folded vs, folded ren_fun]
  have unsat: "la_solver type (concat (map (to_linear_constraints ren_fun) les)) = None"
    by (auto split: option.splits if_splits)
  from la_solver_to_linear_constraints_unsat[OF refl unsat sat inv] show False .
qed

end

datatype hints = LA_Solver la_solver_type

instantiation hints :: default begin
  definition "default = LA_Solver Simplex_Solver"
  instance ..
end

instantiation hints :: showl
begin
fun showsl_hints where
  "showsl_hints (LA_Solver Simplex_Solver) = showsl_lit (STR ''Simplex'')"
definition "showsl_list (xs :: hints list) = default_showsl_list showsl xs"
instance ..
end

context RA_locale begin

definition unsat_checker :: "hints \<Rightarrow> 'v :: {showl,linorder} poly_constraint list \<Rightarrow> showsl check" where
  "unsat_checker hints cnjs = (case hints of
    LA_Solver type \<Rightarrow> 
       case unsat_via_la_solver type cnjs
         of None \<Rightarrow> error (showsl_lit (STR ''could not use linear arithmetic solver to prove unsatisfiability''))
         | Some None \<Rightarrow> return ()
         | Some (Some (vs, \<alpha>)) \<Rightarrow> error (showsl_lit (STR ''the linear inequalities are satisfiable:\<newline>'')
             o showsl_list_gen (\<lambda> v. showsl (var_monom v) o showsl_lit (STR '' := '') o showsl (\<alpha> v) ) (STR '''') (STR '''') (STR ''\<newline>'') (STR '''') vs
           )
    )
  <+? (\<lambda> s. showsl_lit (STR ''The linear inequalities\<newline>  '') \<circ> showsl_sep showsl_poly_constraint (showsl_lit (STR ''\<newline>  '')) cnjs \<circ>
     showsl_lit (STR ''\<newline>cannot be proved unsatisfiable\<newline>  '') \<circ> s)"

lemma unsat_checker:
  assumes ok: "isOK(unsat_checker h cnjs)"
  and "\<And> c. c \<in> set cnjs \<Longrightarrow> interpret_poly_constraint \<alpha> c"
shows False
proof (cases h)
  case (LA_Solver type)
  with ok have "unsat_via_la_solver type cnjs = Some None" by (auto simp: unsat_checker_def split: option.splits)
  from unsat_via_la_solver[OF this assms(2)] show False by auto
qed

subsection \<open>Encoding entailment checking as UNSAT-problems\<close>

fun negate :: "'v RA.exp \<Rightarrow> 'v RA.formula"
where "negate (Fun LessF [a,b]) = Atom (Fun LeF [b,a])"
    | "negate (Fun LeF [a,b]) = Atom (Fun LessF [b,a])"
    | "negate (Fun EqF [a,b]) = Disjunction [Atom (Fun LessF [a,b]), Atom (Fun LessF [b,a])]"
    | "negate _ = Conjunction []"

lemma is_boolE:
  assumes e: "is_bool e"
  and "\<And> s e1 e2. e = Fun s [e1,e2] \<Longrightarrow> s \<in> {LessF, LeF, EqF} \<Longrightarrow> e1 :\<^sub>f RatT \<Longrightarrow> e2 :\<^sub>f RatT \<Longrightarrow> thesis"
  shows "thesis"
proof -
  from e[unfolded is_bool_def] obtain ty where ty: "e :\<^sub>f ty" "ty \<in> {BoolT}" "is_Fun e" by auto
  from ty assms(2) show thesis by (induct e ty rule: has_type_induct, auto)
qed

lemma negate_negates:
  assumes \<alpha>: "assignment \<alpha>" and e: "is_bool e"
  shows "\<alpha> \<Turnstile> negate e \<longleftrightarrow> \<not> \<alpha> \<Turnstile> Atom e"
  using assms by (elim is_boolE, auto)

lemma negate_preserves_is_bool:
  assumes e: "is_bool e"
  shows "formula (negate e)"
  using assms by (elim is_boolE, auto simp: all_less_two)

lemma mono_negate: "mono_formula True (negate e)"
  by (induct e rule: negate.induct, auto)

fun translate_atom
where "translate_atom (Atom e) = e"

definition "translate_atoms = map translate_atom"

fun translate_conj
where "translate_conj (Conjunction \<phi>s) = translate_atoms \<phi>s"

definition check_clause :: "hints \<Rightarrow> 'v::{showl,linorder} RA.formula \<Rightarrow> showsl check"
where "check_clause hints \<phi> \<equiv>
    let es = map RA_exp_to_poly_constraint (translate_conj (\<not>\<^sub>f \<phi>)) in
    unsat_checker hints es
       <+? (\<lambda> s. showsl_lit (STR ''Could not prove unsatisfiability of RA conjunction\<newline>'')
     \<circ> showsl_list_gen showsl_poly_constraint (STR ''False'') (STR '''') (STR '' && '') (STR '''') es \<circ> showsl_nl \<circ> s)"

lemma translate_atom:
  assumes "translate_atom \<phi> = e" and "formula \<phi>" and "is_Atom \<phi>"
  shows "\<phi> \<Longleftrightarrow>\<^sub>f Atom e" by (cases \<phi>, insert assms, auto)

lemma translate_conj:
  assumes es: "translate_conj (\<phi> :: 'v RA.formula) = es"
      and \<phi>: "formula \<phi>" "is_conj_atoms \<phi>"
  shows "\<phi> \<Longleftrightarrow>\<^sub>f conj_atoms es" "e \<in> set es \<Longrightarrow> is_bool e"
proof-
  from \<phi>(2,1) obtain ls where \<phi>: "\<phi> = Conjunction ls" and l: "\<And> l. l \<in> set ls \<Longrightarrow> is_Atom l \<and> formula l"
    by (cases, auto)
  with es have es: "es = map translate_atom ls" by (auto simp: translate_atoms_def)
  show "\<phi> \<Longleftrightarrow>\<^sub>f conj_atoms es"
    using l unfolding \<phi> translate_conj.simps translate_atoms_def es
  proof (induct ls)
    case (Cons l ls)
    from Cons(2)[of l] have "formula l" "is_Atom l" by auto
    from translate_atom[OF refl this] Cons(1)[OF Cons(2)]
    show ?case by auto
  qed auto
  assume "e \<in> set es"
  then show "is_bool e" using l unfolding \<phi> translate_conj.simps translate_atoms_def es
  proof (induct ls)
    case (Cons l ls)
    from Cons(3)[of l] have "formula l" "is_Atom l" by auto
    then have "is_bool (translate_atom l)"
      by (cases l, auto)
    with Cons(1)[OF _ Cons(3)] Cons(2) show ?case by auto
  qed auto
qed

lemma check_clause:
  fixes \<phi> :: "'a::{linorder,showl} RA.formula"
  assumes ok: "isOK (check_clause h \<phi>)" and \<phi>: "formula \<phi>" and clause: "is_neg_atom_clause \<phi>"
  shows "\<Turnstile>\<^sub>f \<phi>"
proof
  fix \<alpha> :: "'a \<times> ty \<Rightarrow> val"
  assume \<alpha>: "assignment \<alpha>"
  show "satisfies \<alpha> \<phi>"
    proof (rule ccontr)
    assume not: "\<not> ?thesis"
    from ok obtain es
    where es: "translate_conj (\<not>\<^sub>f\<phi>) = es"
      and ok: "isOK (unsat_checker h (map RA_exp_to_poly_constraint es))"
      by (unfold check_clause_def, force)
    have "\<not>\<^sub>f \<phi> \<Longleftrightarrow>\<^sub>f conj_atoms es" by (intro translate_conj[OF es], simp add: \<phi> clause,
       rule is_neg_atom_clause.induct[OF clause], auto simp: is_conj_atoms.simps)
    from this \<alpha> not have sat: "\<alpha> \<Turnstile> conj_atoms es" by (auto simp:satisfies_Language)
    show False
    proof(rule unsat_checker[OF ok])
      fix v
      assume v: "v \<in> set (map RA_exp_to_poly_constraint es)"
      then obtain w where w: "w \<in> set es" and v: "v = RA_exp_to_poly_constraint w" by force
      from sat w have eval: "\<alpha> \<Turnstile> Atom w" by auto
      from \<phi> translate_conj(2)[OF es _ _ w] clause
      have "is_bool w" by auto
      from RA_exp_to_poly_constraint[OF \<alpha> this] eval
      show "interpret_poly_constraint (\<lambda>a. to_rat (\<alpha> (a, RatT))) v"
        by (auto simp: v)
    qed
  qed
qed

sublocale logic_checker
  where type_fixer = "TYPE(_)"
    and I = I
    and type_of_fun = type_of_fun
    and Values_of_type = Values_of_type
    and Bool_types = "{BoolT}"
    and to_bool = to_bool
    and logic_checker = check_clause
    and showsl_atom = showsl_RA_exp
    and negate_atom = negate
  by (unfold_locales, auto simp: check_clause negate_negates negate_preserves_is_bool mono_negate)

end
end
