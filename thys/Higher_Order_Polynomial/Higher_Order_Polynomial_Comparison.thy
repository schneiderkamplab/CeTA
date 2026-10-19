theory Higher_Order_Polynomial_Comparison
  imports Higher_Order_Polynomial_Translation
begin

type_synonym 'a ho_nat_poly = "(nat \<times> 'a list) list"

definition ho_monomial_value :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "ho_monomial_value v m = prod_list (map v m)"

fun ho_nat_poly_value :: "('a \<Rightarrow> nat) \<Rightarrow> 'a ho_nat_poly \<Rightarrow> nat" where
  "ho_nat_poly_value v [] = 0"
| "ho_nat_poly_value v ((c,m)#p) = c*ho_monomial_value v m + ho_nat_poly_value v p"

fun ho_monomial_match where
  "ho_monomial_match [] ys = (ys=[])"
| "ho_monomial_match (x#xs) ys = (x\<in>set ys \<and> ho_monomial_match xs (remove1 x ys))"

lemma ho_monomial_remove:
  "x\<in>set xs \<Longrightarrow> ho_monomial_value v xs = v x * ho_monomial_value v (remove1 x xs)"
  by (induction xs) (auto simp: ho_monomial_value_def algebra_simps)

lemma ho_monomial_match_sound:
  "ho_monomial_match xs ys \<Longrightarrow> ho_monomial_value v xs=ho_monomial_value v ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have member: "x\<in>set ys" and rest: "ho_monomial_match xs (remove1 x ys)" by auto
  have eq: "ho_monomial_value v xs=ho_monomial_value v (remove1 x ys)" by (rule Cons.IH[OF rest])
  show ?case using eq ho_monomial_remove[OF member, of v] by (simp add: ho_monomial_value_def)
qed

fun ho_poly_subtract_term where
  "ho_poly_subtract_term c m [] = (if c=0 then Some [] else None)"
| "ho_poly_subtract_term c m ((d,n)#p) =
    (if ho_monomial_match m n then
      (if c\<le>d then Some ((d-c,n)#p) else ho_poly_subtract_term (c-d) m p)
     else map_option (Cons (d,n)) (ho_poly_subtract_term c m p))"

theorem ho_poly_subtract_term_sound:
  "ho_poly_subtract_term c m p=Some q \<Longrightarrow>
    ho_nat_poly_value v p = c*ho_monomial_value v m + ho_nat_poly_value v q"
proof (induction p arbitrary: c q)
  case Nil
  then show ?case by (auto split: if_splits)
next
  case (Cons entry p)
  obtain d n where entry_eq: "entry=(d,n)" by (cases entry) auto
  show ?case
  proof (cases "ho_monomial_match m n")
    case True
    note matched = True
    have mv: "ho_monomial_value v m=ho_monomial_value v n" by (rule ho_monomial_match_sound[OF True])
    show ?thesis
    proof (cases "c\<le>d")
      case True
      have q: "q=(d-c,n)#p" using Cons.prems by (simp add: entry_eq matched True)
      have decomp: "d=c+(d-c)" using True by simp
      have linear: "d*ho_monomial_value v n = c*ho_monomial_value v n + (d-c)*ho_monomial_value v n"
        using arg_cong[OF decomp, where f="\<lambda>i. i*ho_monomial_value v n"] by (simp only: distrib_right)
      show ?thesis unfolding entry_eq q ho_nat_poly_value.simps
        using linear by (simp only: mv; arith)
    next
      case False
      have sub: "ho_poly_subtract_term (c-d) m p=Some q" using Cons.prems by (simp add: entry_eq matched False)
      have ih: "ho_nat_poly_value v p=(c-d)*ho_monomial_value v m+ho_nat_poly_value v q"
        by (rule Cons.IH[OF sub])
      have decomp: "c=d+(c-d)" using False by simp
      have linear: "c*ho_monomial_value v n = d*ho_monomial_value v n + (c-d)*ho_monomial_value v n"
        using arg_cong[OF decomp, where f="\<lambda>i. i*ho_monomial_value v n"] by (simp only: distrib_right)
      show ?thesis unfolding entry_eq ho_nat_poly_value.simps using ih linear by (simp only: mv; arith)
    qed
  next
    case False
    obtain r where sub: "ho_poly_subtract_term c m p=Some r" and q: "q=(d,n)#r"
      using Cons.prems by (auto simp: entry_eq False split: option.splits)
    show ?thesis using Cons.IH[OF sub] by (simp add: entry_eq q algebra_simps)
  qed
qed

fun ho_poly_subtract where
  "ho_poly_subtract p [] = Some p"
| "ho_poly_subtract p ((c,m)#q) = (case ho_poly_subtract_term c m p of
    None \<Rightarrow> None | Some r \<Rightarrow> ho_poly_subtract r q)"

theorem ho_poly_subtract_sound:
  "ho_poly_subtract p q=Some r \<Longrightarrow>
    ho_nat_poly_value v p=ho_nat_poly_value v q+ho_nat_poly_value v r"
proof (induction q arbitrary: p r)
  case Nil
  then show ?case by simp
next
  case (Cons entry q)
  obtain c m where entry_eq: "entry=(c,m)" by (cases entry) auto
  obtain s where first: "ho_poly_subtract_term c m p=Some s" and rest: "ho_poly_subtract s q=Some r"
    using Cons.prems by (auto simp: entry_eq split: option.splits)
  show ?case using ho_poly_subtract_term_sound[OF first, of v] Cons.IH[OF rest]
    by (simp add: entry_eq algebra_simps)
qed

definition ho_poly_positive_constant where
  "ho_poly_positive_constant p = list_ex (\<lambda>(c,m). c>0 \<and> m=[]) p"

lemma ho_poly_positive_constant_sound:
  "ho_poly_positive_constant p \<Longrightarrow> ho_nat_poly_value v p>0"
  by (induction p) (auto simp: ho_poly_positive_constant_def ho_monomial_value_def split: prod.splits)

definition ho_check_nat_poly_ge where
  "ho_check_nat_poly_ge p q = (ho_poly_subtract p q\<noteq>None)"

definition ho_check_nat_poly_gt where
  "ho_check_nat_poly_gt p q = (case ho_poly_subtract p q of None \<Rightarrow> False
    | Some r \<Rightarrow> ho_poly_positive_constant r)"

theorem ho_check_nat_poly_ge_sound:
  "ho_check_nat_poly_ge p q \<Longrightarrow> ho_nat_poly_value v p\<ge>ho_nat_poly_value v q"
  unfolding ho_check_nat_poly_ge_def using ho_poly_subtract_sound[of p q _ v]
  by (cases "ho_poly_subtract p q") auto

theorem ho_check_nat_poly_gt_sound:
  "ho_check_nat_poly_gt p q \<Longrightarrow> ho_nat_poly_value v p>ho_nat_poly_value v q"
  unfolding ho_check_nat_poly_gt_def using ho_poly_subtract_sound[of p q _ v] ho_poly_positive_constant_sound[of _ v]
  by (cases "ho_poly_subtract p q") auto

lemma ho_monomial_append:
  "ho_monomial_value v (m@n)=ho_monomial_value v m*ho_monomial_value v n"
  by (simp add: ho_monomial_value_def)

lemma ho_nat_poly_append:
  "ho_nat_poly_value v (p@q)=ho_nat_poly_value v p+ho_nat_poly_value v q"
  by (induction p) (auto simp: algebra_simps split: prod.splits)

definition ho_nat_poly_times where
  "ho_nat_poly_times p q = concat (map (\<lambda>(c,m). map (\<lambda>(d,n). (c*d,m@n)) q) p)"

lemma ho_nat_poly_scale:
  "ho_nat_poly_value v (map (\<lambda>(d,n). (c*d,m@n)) q) =
    c*ho_monomial_value v m*ho_nat_poly_value v q"
  by (induction q) (auto simp: ho_monomial_append algebra_simps split: prod.splits)

lemma ho_nat_poly_times_value:
  "ho_nat_poly_value v (ho_nat_poly_times p q)=ho_nat_poly_value v p*ho_nat_poly_value v q"
  by (induction p) (auto simp: ho_nat_poly_times_def ho_nat_poly_append ho_nat_poly_scale algebra_simps split: prod.splits)

fun ho_polynomial_coefficients where
  "ho_polynomial_coefficients (HPNumber b n) = [(n,[])]"
| "ho_polynomial_coefficients (HPAdd b p q) = ho_polynomial_coefficients p @ ho_polynomial_coefficients q"
| "ho_polynomial_coefficients (HPMultiply b p q) = ho_nat_poly_times (ho_polynomial_coefficients p) (ho_polynomial_coefficients q)"
| "ho_polynomial_coefficients p = [(1,[p])]"

definition ho_polynomial_atom_value where
  "ho_polynomial_atom_value e p = ho_observe (HBase 0) (ho_polynomial_eval e p)"

lemma ho_polynomial_atom_numeral:
  assumes ty: "ho_polynomial_type G p (HBase b)" and ev: "ho_env_value G e"
  shows "ho_numeral (ho_polynomial_eval e p) (ho_polynomial_atom_value e p)"
proof -
  have v: "ho_value (HBase b) (ho_polynomial_eval e p)"
    by (rule ho_polynomial_fundamental[OF ty, THEN conjunct1, rule_format, OF ev])
  then obtain n where num: "ho_numeral (ho_polynomial_eval e p) n" by auto
  show ?thesis unfolding ho_polynomial_atom_value_def using num ho_observe_numeral[OF num] by simp
qed

theorem ho_polynomial_coefficients_sound:
  assumes ty: "ho_polynomial_type G p (HBase b)" and ev: "ho_env_value G e"
  shows "ho_numeral (ho_polynomial_eval e p)
    (ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients p))"
using ty ev
proof (induction p arbitrary: G b)
  case (HPVar n)
  then show ?case using ho_polynomial_atom_numeral[OF HPVar.prems]
    by (simp add: ho_monomial_value_def)
next
  case (HPNumber c n)
  show ?case by (simp add: ho_monomial_value_def)
next
  case (HPAdd c p q)
  obtain a d where p: "ho_polynomial_type G p (HBase a)" and q: "ho_polynomial_type G q (HBase d)"
    using HPAdd.prems(1) by cases auto
  show ?case using ho_add_numeral[OF HPAdd.IH(1)[OF p HPAdd.prems(2)] HPAdd.IH(2)[OF q HPAdd.prems(2)]]
    by (simp add: ho_nat_poly_append)
next
  case (HPMultiply c p q)
  obtain a d where p: "ho_polynomial_type G p (HBase a)" and q: "ho_polynomial_type G q (HBase d)"
    using HPMultiply.prems(1) by cases auto
  show ?case using ho_multiply_numeral[OF HPMultiply.IH(1)[OF p HPMultiply.prems(2)] HPMultiply.IH(2)[OF q HPMultiply.prems(2)]]
    by (simp add: ho_nat_poly_times_value)
next
  case (HPApply A B f x)
  then show ?case using ho_polynomial_atom_numeral[OF HPApply.prems]
    by (simp add: ho_monomial_value_def)
next
  case (HPAbstract A B t)
  from HPAbstract.prems(1) show ?case by cases
qed

definition ho_check_base_polynomial_ge where
  "ho_check_base_polynomial_ge G b p q =
    (ho_polynomial_typeof G p=Some (HBase b) \<and> ho_polynomial_typeof G q=Some (HBase b) \<and>
     ho_check_nat_poly_ge (ho_polynomial_coefficients p) (ho_polynomial_coefficients q))"

definition ho_check_base_polynomial_gt where
  "ho_check_base_polynomial_gt G b p q =
    (ho_polynomial_typeof G p=Some (HBase b) \<and> ho_polynomial_typeof G q=Some (HBase b) \<and>
     ho_check_nat_poly_gt (ho_polynomial_coefficients p) (ho_polynomial_coefficients q))"

theorem ho_check_base_polynomial_ge_sound:
  assumes check: "ho_check_base_polynomial_ge G b p q" and ev: "ho_env_value G e"
  shows "ho_value_ge (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof -
  have p: "ho_polynomial_type G p (HBase b)" and q: "ho_polynomial_type G q (HBase b)"
    using check unfolding ho_check_base_polynomial_ge_def by (auto intro: ho_polynomial_typeof_sound)
  have ge: "ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients p) \<ge>
      ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients q)"
    by (rule ho_check_nat_poly_ge_sound) (use check in \<open>simp add: ho_check_base_polynomial_ge_def\<close>)
  show ?thesis unfolding ho_value_ge.simps
    using ho_polynomial_coefficients_sound[OF p ev] ho_polynomial_coefficients_sound[OF q ev] ge by blast
qed

theorem ho_check_base_polynomial_gt_sound:
  assumes check: "ho_check_base_polynomial_gt G b p q" and ev: "ho_env_value G e"
  shows "ho_value_gt (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof -
  have p: "ho_polynomial_type G p (HBase b)" and q: "ho_polynomial_type G q (HBase b)"
    using check unfolding ho_check_base_polynomial_gt_def by (auto intro: ho_polynomial_typeof_sound)
  have gt: "ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients p) >
      ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients q)"
    by (rule ho_check_nat_poly_gt_sound) (use check in \<open>simp add: ho_check_base_polynomial_gt_def\<close>)
  show ?thesis unfolding ho_value_gt.simps
    using ho_polynomial_coefficients_sound[OF p ev] ho_polynomial_coefficients_sound[OF q ev] gt by blast
qed

end
