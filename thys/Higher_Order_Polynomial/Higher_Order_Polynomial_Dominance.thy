theory Higher_Order_Polynomial_Dominance
  imports Higher_Order_Polynomial_Comparison
begin

text \<open>Coefficient matching may use independently verified atom inequalities,
not only syntactic equality. This layer is independent of the atom language.\<close>

fun ho_monomial_dominates where
  "ho_monomial_dominates R [] ys = (ys = [])"
| "ho_monomial_dominates R (x#xs) ys =
    list_ex (\<lambda>y. R x y \<and> ho_monomial_dominates R xs (remove1 y ys)) ys"

theorem ho_monomial_dominates_sound:
  assumes rel: "\<And>x y. R x y \<Longrightarrow> v x \<ge> v y"
  shows "ho_monomial_dominates R xs ys \<Longrightarrow>
    ho_monomial_value v xs \<ge> ho_monomial_value v ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y where member: "y \<in> set ys" and xy: "R x y"
    and rest: "ho_monomial_dominates R xs (remove1 y ys)"
    using Cons.prems by (auto simp: list_ex_iff)
  have ih: "ho_monomial_value v (remove1 y ys) \<le> ho_monomial_value v xs"
    by (rule Cons.IH[OF rest])
  have product: "v y * ho_monomial_value v (remove1 y ys) \<le>
    v x * ho_monomial_value v xs" by (rule mult_le_mono[OF rel[OF xy] ih])
  show ?case using product ho_monomial_remove[OF member, of v]
    by (simp add: ho_monomial_value_def)
qed

fun ho_poly_consume_term where
  "ho_poly_consume_term R c m [] = (if c=0 then Some [] else None)"
| "ho_poly_consume_term R c m ((d,n)#p) =
    (if ho_monomial_dominates R n m then
      (if c\<le>d then Some ((d-c,n)#p) else ho_poly_consume_term R (c-d) m p)
     else map_option (Cons (d,n)) (ho_poly_consume_term R c m p))"

theorem ho_poly_consume_term_sound:
  assumes rel: "\<And>x y. R x y \<Longrightarrow> v x \<ge> v y"
  shows "ho_poly_consume_term R c m p=Some q \<Longrightarrow>
    ho_nat_poly_value v p \<ge> c*ho_monomial_value v m + ho_nat_poly_value v q"
proof (induction p arbitrary: c q)
  case Nil
  then show ?case by (auto split: if_splits)
next
  case (Cons entry p)
  obtain d n where entry_eq: "entry=(d,n)" by (cases entry) auto
  show ?case
  proof (cases "ho_monomial_dominates R n m")
    case True
    note matched = True
    have mv: "ho_monomial_value v m \<le> ho_monomial_value v n"
      by (rule ho_monomial_dominates_sound[OF rel True])
    show ?thesis
    proof (cases "c\<le>d")
      case True
      have q: "q=(d-c,n)#p" using Cons.prems by (simp add: entry_eq matched True)
      have decomp: "d=c+(d-c)" using True by simp
      have linear: "d*ho_monomial_value v n = c*ho_monomial_value v n + (d-c)*ho_monomial_value v n"
        using arg_cong[OF decomp, where f="\<lambda>i. i*ho_monomial_value v n"] by (simp only: distrib_right)
      have bounded: "c*ho_monomial_value v m \<le> c*ho_monomial_value v n"
        by (rule mult_le_mono2[OF mv])
      show ?thesis unfolding entry_eq q ho_nat_poly_value.simps using linear bounded by arith
    next
      case False
      have sub: "ho_poly_consume_term R (c-d) m p=Some q"
        using Cons.prems by (simp add: entry_eq matched False)
      have ih: "(c-d)*ho_monomial_value v m+ho_nat_poly_value v q \<le> ho_nat_poly_value v p"
        by (rule Cons.IH[OF sub])
      have decomp: "c=d+(c-d)" using False by simp
      have linear: "c*ho_monomial_value v m = d*ho_monomial_value v m + (c-d)*ho_monomial_value v m"
        using arg_cong[OF decomp, where f="\<lambda>i. i*ho_monomial_value v m"] by (simp only: distrib_right)
      have bounded: "d*ho_monomial_value v m \<le> d*ho_monomial_value v n"
        by (rule mult_le_mono2[OF mv])
      show ?thesis unfolding entry_eq ho_nat_poly_value.simps using ih linear bounded by arith
    qed
  next
    case False
    obtain r where sub: "ho_poly_consume_term R c m p=Some r" and q: "q=(d,n)#r"
      using Cons.prems by (auto simp: entry_eq False split: option.splits)
    show ?thesis using Cons.IH[OF sub] by (simp add: entry_eq q algebra_simps)
  qed
qed

fun ho_poly_consume where
  "ho_poly_consume R p [] = Some p"
| "ho_poly_consume R p ((c,m)#q) = (case ho_poly_consume_term R c m p of
    None \<Rightarrow> None | Some r \<Rightarrow> ho_poly_consume R r q)"

theorem ho_poly_consume_sound:
  assumes rel: "\<And>x y. R x y \<Longrightarrow> v x \<ge> v y"
  shows "ho_poly_consume R p q=Some r \<Longrightarrow>
    ho_nat_poly_value v p \<ge> ho_nat_poly_value v q+ho_nat_poly_value v r"
proof (induction q arbitrary: p r)
  case Nil
  then show ?case by simp
next
  case (Cons entry q)
  obtain c m where entry_eq: "entry=(c,m)" by (cases entry) auto
  obtain t where sub: "ho_poly_consume_term R c m p=Some t" and rest: "ho_poly_consume R t q=Some r"
    using Cons.prems by (auto simp: entry_eq split: option.splits)
  have bounded: "c*ho_monomial_value v m + ho_nat_poly_value v t \<le> ho_nat_poly_value v p"
    by (rule ho_poly_consume_term_sound[where R=R and v=v, OF rel sub])
  show ?case using bounded Cons.IH[OF rest]
    by (simp only: entry_eq ho_nat_poly_value.simps; arith)
qed

fun ho_structural_polynomial_ge where
  "ho_structural_polynomial_ge 0 G A p q = (p=q \<and> ho_polynomial_typeof G p=Some A)"
| "ho_structural_polynomial_ge (Suc fuel) G A p q =
    (ho_polynomial_typeof G p=Some A \<and> ho_polynomial_typeof G q=Some A \<and>
     (p=q \<or>
      (case A of HBase b \<Rightarrow> ho_check_base_polynomial_ge G b p q | _ \<Rightarrow> False) \<or>
      (case (p,q) of (HPApply B C f x,HPApply D E g y) \<Rightarrow>
        B=D \<and> C=A \<and> E=A \<and>
        ho_structural_polynomial_ge fuel G (HArrow B A) f g \<and>
        ho_structural_polynomial_ge fuel G B x y
       | _ \<Rightarrow> False)))"

lemma ho_polynomial_application_ge:
  assumes ft: "ho_polynomial_type G f (HArrow A B)"
    and xt: "ho_polynomial_type G x A" and yt: "ho_polynomial_type G y A"
    and ev: "ho_env_value G e"
    and fg: "ho_value_ge (HArrow A B) (ho_polynomial_eval e f) (ho_polynomial_eval e g)"
    and xy: "ho_value_ge A (ho_polynomial_eval e x) (ho_polynomial_eval e y)"
  shows "ho_value_ge B (App (ho_polynomial_eval e f) (ho_polynomial_eval e x))
    (App (ho_polynomial_eval e g) (ho_polynomial_eval e y))"
proof -
  have fv: "ho_value (HArrow A B) (ho_polynomial_eval e f)"
    by (rule ho_polynomial_fundamental[OF ft, THEN conjunct1, rule_format, OF ev])
  have xv: "ho_value A (ho_polynomial_eval e x)"
    by (rule ho_polynomial_fundamental[OF xt, THEN conjunct1, rule_format, OF ev])
  have yv: "ho_value A (ho_polynomial_eval e y)"
    by (rule ho_polynomial_fundamental[OF yt, THEN conjunct1, rule_format, OF ev])
  have first: "ho_value_ge B (App (ho_polynomial_eval e f) (ho_polynomial_eval e x))
      (App (ho_polynomial_eval e f) (ho_polynomial_eval e y))" using fv xv yv xy by simp
  have second: "ho_value_ge B (App (ho_polynomial_eval e f) (ho_polynomial_eval e y))
      (App (ho_polynomial_eval e g) (ho_polynomial_eval e y))" using fg yv by simp
  show ?thesis by (rule ho_value_ge_trans[OF first second])
qed

theorem ho_structural_polynomial_ge_sound:
  "ho_structural_polynomial_ge fuel G A p q \<Longrightarrow> ho_env_value G e \<Longrightarrow>
    ho_value_ge A (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof (induction fuel arbitrary: G A p q e)
  case 0
  have ev: "ho_env_value G e" using 0 by auto
  have ty: "ho_polynomial_type G p A" and eq: "p=q"
    using 0 by (auto intro: ho_polynomial_typeof_sound)
  show ?case using ho_polynomial_fundamental[OF ty, THEN conjunct1, rule_format, OF ev] eq
    by (auto intro: ho_value_ge_refl)
next
  case (Suc fuel)
  have pt: "ho_polynomial_type G p A" and qt: "ho_polynomial_type G q A"
    using Suc.prems(1) by (auto intro: ho_polynomial_typeof_sound)
  show ?case
  proof (cases "p=q")
    case True
    show ?thesis using ho_polynomial_fundamental[OF pt, THEN conjunct1, rule_format, OF Suc.prems(2)] True
      by (auto intro: ho_value_ge_refl)
  next
    case False
    show ?thesis
    proof (cases "case A of HBase b \<Rightarrow> ho_check_base_polynomial_ge G b p q | _ \<Rightarrow> False")
      case True
      then obtain b where "A=HBase b" and "ho_check_base_polynomial_ge G b p q" by (cases A) auto
      then show ?thesis using ho_check_base_polynomial_ge_sound[OF _ Suc.prems(2)] by blast
    next
      case False
      obtain B f x g y where p: "p=HPApply B A f x" and q: "q=HPApply B A g y"
        and fg: "ho_structural_polynomial_ge fuel G (HArrow B A) f g"
        and xy: "ho_structural_polynomial_ge fuel G B x y"
        using Suc.prems(1) False \<open>p\<noteq>q\<close>
        by (auto split: ho_polynomial.splits)
      have ft: "ho_polynomial_type G f (HArrow B A)"
        using pt unfolding p by cases auto
      have xt: "ho_polynomial_type G x B"
        using pt unfolding p by cases auto
      have yt: "ho_polynomial_type G y B" using qt unfolding q by cases auto
      have fge: "ho_value_ge (HArrow B A) (ho_polynomial_eval e f) (ho_polynomial_eval e g)"
        by (rule Suc.IH[OF fg Suc.prems(2)])
      have xge: "ho_value_ge B (ho_polynomial_eval e x) (ho_polynomial_eval e y)"
        by (rule Suc.IH[OF xy Suc.prems(2)])
      show ?thesis unfolding p q ho_polynomial_eval.simps
        by (rule ho_polynomial_application_ge[OF ft xt yt Suc.prems(2) fge xge])
    qed
  qed
qed

fun ho_function_atom_dominates where
  "ho_function_atom_dominates G (HPApply (HBase a) (HBase b) f x)
      (HPApply (HBase c) (HBase d) g y) =
    (a=c \<and> b=d \<and> f=g \<and>
      ho_polynomial_typeof G f=Some (HArrow (HBase a) (HBase b)) \<and>
      ho_check_base_polynomial_ge G a x y)"
| "ho_function_atom_dominates G p q = (p=q)"

lemma ho_base_observe_ge:
  "ho_value_ge (HBase b) p q \<Longrightarrow>
    ho_observe (HBase 0) p \<ge> ho_observe (HBase 0) q"
  using ho_observe_numeral by auto

lemma ho_function_application_dominates:
  assumes f: "ho_polynomial_typeof G f=Some (HArrow (HBase a) (HBase b))"
    and xy: "ho_check_base_polynomial_ge G a x y" and ev: "ho_env_value G e"
  shows "ho_polynomial_atom_value e (HPApply (HBase a) (HBase b) f x) \<ge>
    ho_polynomial_atom_value e (HPApply (HBase a) (HBase b) f y)"
proof -
  have ft: "ho_polynomial_type G f (HArrow (HBase a) (HBase b))"
    by (rule ho_polynomial_typeof_sound[OF f])
  have xt: "ho_polynomial_type G x (HBase a)" and yt: "ho_polynomial_type G y (HBase a)"
    using xy unfolding ho_check_base_polynomial_ge_def by (auto intro: ho_polynomial_typeof_sound)
  have fv: "ho_value (HArrow (HBase a) (HBase b)) (ho_polynomial_eval e f)"
    by (rule ho_polynomial_fundamental[OF ft, THEN conjunct1, rule_format, OF ev])
  have xv: "ho_value (HBase a) (ho_polynomial_eval e x)"
    by (rule ho_polynomial_fundamental[OF xt, THEN conjunct1, rule_format, OF ev])
  have yv: "ho_value (HBase a) (ho_polynomial_eval e y)"
    by (rule ho_polynomial_fundamental[OF yt, THEN conjunct1, rule_format, OF ev])
  have ge: "ho_value_ge (HBase a) (ho_polynomial_eval e x) (ho_polynomial_eval e y)"
    by (rule ho_check_base_polynomial_ge_sound[OF xy ev])
  have app: "ho_value_ge (HBase b) (App (ho_polynomial_eval e f) (ho_polynomial_eval e x))
    (App (ho_polynomial_eval e f) (ho_polynomial_eval e y))"
    using fv xv yv ge by simp
  show ?thesis using ho_base_observe_ge[OF app]
    by (simp add: ho_polynomial_atom_value_def)
qed

theorem ho_function_atom_dominates_sound:
  "ho_function_atom_dominates G p q \<Longrightarrow> ho_env_value G e \<Longrightarrow>
    ho_polynomial_atom_value e p \<ge> ho_polynomial_atom_value e q"
  by (induction G p q rule: ho_function_atom_dominates.induct)
     (auto intro: ho_function_application_dominates)

definition ho_curried_atom_dominates where
  "ho_curried_atom_dominates G p q = (ho_function_atom_dominates G p q \<or>
    (case ho_polynomial_typeof G p of Some (HBase b) \<Rightarrow>
      ho_structural_polynomial_ge 16 G (HBase b) p q | _ \<Rightarrow> False))"

lemma ho_curried_atom_dominates_sound:
  assumes check: "ho_curried_atom_dominates G p q" and ev: "ho_env_value G e"
  shows "ho_polynomial_atom_value e p \<ge> ho_polynomial_atom_value e q"
proof (cases "ho_function_atom_dominates G p q")
  case True
  show ?thesis by (rule ho_function_atom_dominates_sound[OF True ev])
next
  case False
  obtain b where ge: "ho_structural_polynomial_ge 16 G (HBase b) p q"
    using check False unfolding ho_curried_atom_dominates_def
    by (auto split: option.splits ho_type.splits)
  show ?thesis using ho_base_observe_ge[OF ho_structural_polynomial_ge_sound[OF ge ev]]
    by (simp add: ho_polynomial_atom_value_def)
qed

definition ho_check_monotone_base_ge where
  "ho_check_monotone_base_ge G b p q =
    (ho_polynomial_typeof G p=Some (HBase b) \<and> ho_polynomial_typeof G q=Some (HBase b) \<and>
     ho_poly_consume (ho_curried_atom_dominates G)
       (ho_polynomial_coefficients p) (ho_polynomial_coefficients q) \<noteq> None)"

definition ho_check_monotone_base_gt where
  "ho_check_monotone_base_gt G b p q =
    (ho_polynomial_typeof G p=Some (HBase b) \<and> ho_polynomial_typeof G q=Some (HBase b) \<and>
     (case ho_poly_consume (ho_curried_atom_dominates G)
       (ho_polynomial_coefficients p) (ho_polynomial_coefficients q) of None \<Rightarrow> False
       | Some r \<Rightarrow> ho_poly_positive_constant r))"

lemma ho_function_poly_consume_sound:
  assumes ev: "ho_env_value G e"
    and check: "ho_poly_consume (ho_curried_atom_dominates G) p q=Some r"
  shows "ho_nat_poly_value (ho_polynomial_atom_value e) p \<ge>
    ho_nat_poly_value (ho_polynomial_atom_value e) q + ho_nat_poly_value (ho_polynomial_atom_value e) r"
  by (rule ho_poly_consume_sound[where R="ho_curried_atom_dominates G" and v="ho_polynomial_atom_value e", OF _ check])
     (use ev in \<open>auto intro: ho_curried_atom_dominates_sound\<close>)

theorem ho_check_monotone_base_ge_sound:
  assumes check: "ho_check_monotone_base_ge G b p q" and ev: "ho_env_value G e"
  shows "ho_value_ge (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof -
  have p: "ho_polynomial_type G p (HBase b)" and q: "ho_polynomial_type G q (HBase b)"
    using check unfolding ho_check_monotone_base_ge_def by (auto intro: ho_polynomial_typeof_sound)
  obtain r where sub: "ho_poly_consume (ho_curried_atom_dominates G)
    (ho_polynomial_coefficients p) (ho_polynomial_coefficients q)=Some r"
    using check unfolding ho_check_monotone_base_ge_def by (cases "ho_poly_consume (ho_curried_atom_dominates G)
      (ho_polynomial_coefficients p) (ho_polynomial_coefficients q)") auto
  have ge: "ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients p) \<ge>
    ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients q)"
    using ho_function_poly_consume_sound[OF ev sub] by arith
  show ?thesis unfolding ho_value_ge.simps
    using ho_polynomial_coefficients_sound[OF p ev] ho_polynomial_coefficients_sound[OF q ev] ge by blast
qed

theorem ho_check_monotone_base_gt_sound:
  assumes check: "ho_check_monotone_base_gt G b p q" and ev: "ho_env_value G e"
  shows "ho_value_gt (HBase b) (ho_polynomial_eval e p) (ho_polynomial_eval e q)"
proof -
  have p: "ho_polynomial_type G p (HBase b)" and q: "ho_polynomial_type G q (HBase b)"
    using check unfolding ho_check_monotone_base_gt_def by (auto intro: ho_polynomial_typeof_sound)
  obtain r where sub: "ho_poly_consume (ho_curried_atom_dominates G)
    (ho_polynomial_coefficients p) (ho_polynomial_coefficients q)=Some r"
    and positive: "ho_poly_positive_constant r"
    using check unfolding ho_check_monotone_base_gt_def by (auto split: option.splits)
  have gt: "ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients p) >
    ho_nat_poly_value (ho_polynomial_atom_value e) (ho_polynomial_coefficients q)"
    using ho_function_poly_consume_sound[OF ev sub]
      ho_poly_positive_constant_sound[OF positive, where v="ho_polynomial_atom_value e"] by arith
  show ?thesis unfolding ho_value_gt.simps
    using ho_polynomial_coefficients_sound[OF p ev] ho_polynomial_coefficients_sound[OF q ev] gt by blast
qed

end
