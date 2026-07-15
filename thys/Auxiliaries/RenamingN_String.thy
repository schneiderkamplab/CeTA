theory RenamingN_String 
  imports 
    RenamingN
    Show.Number_Parser
    First_Order_Terms.Lists_are_Infinite
begin

lemma underscore_not_show: "CHR ''_'' \<notin> set (show (n :: nat))"
  using set_show_nat[of n] unfolding digits_def by auto

lemma append_Cons_eq_iff':
  "x \<notin> set xs \<Longrightarrow> x \<notin> set xs' \<Longrightarrow>
   xs @ x # ys = xs' @ x # ys' \<longleftrightarrow> (xs = xs' \<and> ys = ys')"
  by (auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)

definition x_var_list :: "nat \<times> string \<Rightarrow> string"
  where "x_var_list ns \<equiv> case ns of (n, s) \<Rightarrow> CHR ''x'' # show n @ ''_'' @ s"

lemma inj_x_var_list: "inj x_var_list" 
  unfolding x_var_list_def inj_def 
proof (clarify, goal_cases)
  case (1 n1 x1 n2 x2)
  from 1 append_Cons_eq_iff'[OF underscore_not_show[of n1] underscore_not_show[of n2], of x1 x2]
  have n: "show n1 = show n2" and x: "x1 = x2" by auto
  with inj_show_nat have "n1 = n2" by (auto simp: inj_def)
  with x show ?case by auto
qed    

lift_definition string_renameN :: "string renamingN" is "(x_var_list, Cons (CHR ''y''))" 
  using inj_x_var_list
  by (auto simp: x_var_list_def)

(* and now the same for string literals *)
definition x_var_list_lit :: "nat \<times> String.literal \<Rightarrow> String.literal" where
  "x_var_list_lit ns = (case ns of (n,s) \<Rightarrow> STR ''x'' + String.implode (show n) + STR ''_'' + s)" 

lemma underscore_not_ascii_show: "CHR ''_'' \<notin> set (map String.ascii_of (show (n :: nat)))" 
  using set_show_nat[of n] unfolding digits_def
  by auto
  

lemma inj_x_var_list_lit: "inj x_var_list_lit" 
  unfolding x_var_list_lit_def inj_def
proof (clarify, goal_cases)
  case (1 n1 s1 n2 s2)
  define pre where "pre = STR ''x'' + String.implode (show n1) + STR ''_''" 
  note [simp] = plus_literal.rep_eq
  have [simp]: "literal.explode STR ''_'' = ''_''" by code_simp
  from arg_cong[OF 1, of String.explode, simplified] 
    append_Cons_eq_iff'[OF underscore_not_ascii_show[of n1] underscore_not_ascii_show[of n2]]
  have "map String.ascii_of (show n1) = map String.ascii_of (show n2)" by auto
  also have "\<dots> = map id (show n2)" 
    by (intro map_cong refl, insert set_show_nat[of n2], auto simp: digits_def)
  also have "map String.ascii_of (show n1) = map id (show n1)" 
    by (intro map_cong refl, insert set_show_nat[of n1], auto simp: digits_def)
  finally have n2: "n2 = n1" using inj_show_nat by (auto simp: inj_on_def)
  from 1[unfolded n2] have "pre + s1 = pre + s2" 
    unfolding pre_def by auto
  hence "s1 = s2"
    by (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)
  with n2 show ?case by auto
qed

instance String.literal :: infinite
proof
  show "infinite (UNIV :: String.literal set)" 
    by (rule String.infinite_literal)
qed

lift_definition string_lit_renameN :: "String.literal renamingN" is "(x_var_list_lit, (\<lambda> s. (STR ''y'' + s)))" 
proof (intro exI conjI, rule refl)
  show "inj x_var_list_lit" by (rule inj_x_var_list_lit)
  show "inj ((+) STR ''y'')" unfolding inj_on_def by auto (metis String.implode_explode_eq plus_literal.rep_eq same_append_eq)
  show "range x_var_list_lit \<inter> range ((+) STR ''y'') = {}" 
    unfolding x_var_list_lit_def
    by (auto simp: add_Literal_assoc)
qed
end