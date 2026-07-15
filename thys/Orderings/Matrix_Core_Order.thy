theory Matrix_Core_Order
  imports 
    Linear_Polynomial
    Matrix_Base
    Monotone_Algebra
    Reduction_Pair
begin

class SN_delta_order = linordered_idom + ordered_semiring_1 + 
  assumes SN_delta: "(\<delta> :: 'a) > 0 \<Longrightarrow> SN {(x, y). 0 \<le> y \<and> \<delta> \<le> x - y}" 
  and mult_nonneg_imp_neg: "(\<forall> x \<ge> 0. (d :: 'a) * x \<ge> c) \<Longrightarrow> d \<ge> 0"  

context floor_ceiling
begin
subclass SN_delta_order
proof
  fix \<delta> :: 'a
  assume pos: "0 < \<delta>" 
  show "SN {(x, y). 0 \<le> y \<and> \<delta> \<le> x - y}" 
  proof 
    fix f
    assume steps: "\<forall>i. (f i, f (Suc i)) \<in> {(x, y). 0 \<le> y \<and> \<delta> \<le> x - y}" 
    define g where "g = f o Suc" 
    have g: "g i \<ge> 0" for i unfolding g_def using steps by auto
    have steps: "\<And> i. (g i, g (Suc i)) \<in> {(x, y). 0 \<le> y \<and> \<delta> \<le> x - y}" 
      unfolding g_def using steps by auto
    define bnd where "bnd = g 0 / \<delta>" 
    have "g i \<le> g 0 - \<delta> * of_nat i" for i
    proof (induct i)
      case (Suc i)
      from steps[of i] 
      have "g (Suc i) \<le> g i - \<delta>" by (auto simp: field_simps)
      also have "\<dots> \<le> g 0 - \<delta> * of_nat i - \<delta>" using Suc by (simp add: diff_right_mono)
      finally show ?case
        by (simp add: local.diff_add_eq_diff_diff_swap local.distrib_left)
    qed auto
    with g have "\<delta> * of_nat i \<le> g 0" for i 
      by (meson diff_ge_0_iff_ge dual_order.trans)
    with pos have "of_nat i \<le> bnd" for i unfolding bnd_def
      using le_divide_eq mult_of_nat_commute by auto
    thus False using add_le_same_cancel2 ex_large_of_nat not_one_le_zero order_trans by blast
  qed
next
  fix c d :: 'a
  assume "\<forall> x \<ge> 0. c \<le> d * x" 
  hence ge: "\<And> x. x \<ge> 0 \<Longrightarrow> c \<le> d * x" by auto
  show "0 \<le> d"
  proof (cases "c \<ge> 0")
    case True
    with ge[of 1] show ?thesis by auto
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence d: "d < 0" by auto
      hence "x \<ge> 0 \<Longrightarrow> c / d \<ge> x" for x using ge[of x]
        by (metis local.divide_le_cancel local.nle_le local.nonzero_mult_div_cancel_left) 
      thus False 
        by (metis False d abs_ge_zero abs_le_self_iff add_le_same_cancel1 mult_not_zero neg_divide_le_eq
            zero_le_double_add_iff_zero_le_single_add)
    qed
  qed
qed
end

instance int :: SN_delta_order
proof
  fix \<delta> :: int
  show "0 < \<delta> \<Longrightarrow> SN {(x, y). 0 \<le> y \<and> \<delta> \<le> x - y}" 
    by (intro SN_subset[OF int_SN.SN], auto)
next
  fix c d :: int
  assume "\<forall>x\<ge>0. c \<le> d * x"
  hence ge: "\<And> x. x \<ge> 0 \<Longrightarrow> c \<le> d * x" by auto
  show "0 \<le> d"
  proof (cases "c \<ge> 0")
    case True
    with ge[of 1] show ?thesis by auto
  next
    case False
    hence c: "c < 0" by auto
    define e where "e = - c" 
    have e: "e \<ge> 0" "e > 0" using c unfolding e_def by auto
    show ?thesis
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence d: "d < 0" by auto
      with ge[OF e(1), unfolded e_def] have "c * (1 + d) \<le> 0" by (auto simp: algebra_simps)
      with c have "(1 + d) \<ge> 0" by (simp add: mult_le_0_iff)
      with d have d: "d = -1" by auto
      have "x \<ge> 0 \<Longrightarrow> x \<le> -c" for x using ge[of x] unfolding d by (auto simp: algebra_simps)
      thus False by presburger
    qed
  qed
qed


locale core_mat_inter =   
  fixes n :: nat
  and \<delta> :: "'a :: SN_delta_order" 
begin

sublocale squared_ring_mat n "\<lambda> x y. x - y \<ge> \<delta>"  .

abbreviation mat_add_mon :: "'a mat monoid" where 
  "mat_add_mon \<equiv> \<lparr>carrier = carrier_mat n n, mult = (+), one = 0\<^sub>m n n\<rparr>"

abbreviation mat_sq_ring :: "'a mat ring" where
  "mat_sq_ring \<equiv> ring_mat TYPE('a) n ()"  

definition sum_list_mat where "sum_list_mat \<equiv> list_prod mat_add_mon" 

lemma sum_list_mat_carrier[simp,intro]: "set as \<subseteq> carrier_mat n n \<Longrightarrow> sum_list_mat as \<in> carrier_mat n n" 
  unfolding sum_list_mat_def using wf_list_prod_gen[of mat_add_mon mat_add_mon as]
  by auto

lemma sum_list_mat_simps[simp]: "sum_list_mat [] = 0\<^sub>m n n" 
    "sum_list_mat (x # xs) = x + sum_list_mat xs" 
  unfolding sum_list_mat_def by auto

lemma sum_list_mat_N[intro]: "set as \<subseteq> N \<Longrightarrow> sum_list_mat as \<in> N" 
  by (induct as, auto simp: N_add_closed)


lemma N_carrier: "N \<subseteq> carrier_mat n n" 
  unfolding N_def by auto

definition default_Alpha :: "'a mat \<Rightarrow> 'f \<times> nat \<Rightarrow> 'a mat list \<times> 'a mat" where
  "default_Alpha def fk = (let k = snd fk in (replicate k (1\<^sub>m n), def))"

definition Alpha_list_to_Alpha where 
  "Alpha_list_to_Alpha def fk_cs fk = (case map_of fk_cs fk of None \<Rightarrow> default_Alpha def fk | Some i \<Rightarrow> i)" 

lemma sum_list_mat_append: "set as \<subseteq> carrier_mat n n \<Longrightarrow> set bs \<subseteq> carrier_mat n n \<Longrightarrow>
   sum_list_mat (as @ bs) = sum_list_mat as + sum_list_mat bs"
  by (induct as, auto)

lemma sum_list_split: assumes "set as \<subseteq> carrier_mat n n"
  and "i < length as" 
shows "sum_list_mat as = as ! i + sum_list_mat (take i as @ drop (Suc i) as)" 
proof -
  define bef where "bef = take i as" 
  define aft where "aft = drop (Suc i) as" 
  from assms have as: "as = bef @ as ! i # aft" 
    by (auto simp: id_take_nth_drop bef_def aft_def)
  have carr: "set bef \<subseteq> carrier_mat n n" "set aft \<subseteq> carrier_mat n n" "as ! i \<in> carrier_mat n n" 
    subgoal using assms by (subst (asm) as) auto
    subgoal using assms by (subst (asm) as) auto
    subgoal using assms by (subst (asm) as) auto
    done
  show ?thesis unfolding bef_def[symmetric] aft_def[symmetric]
    apply (subst as)
    apply (subst (1 2) sum_list_mat_append)
    by (insert carr, auto)
qed

context (* fixes Alpha parameter and type of variables *)
  fixes Alpha :: "'f \<times> nat \<Rightarrow> 'a mat list \<times> 'a mat" 
  and "typ" :: "'v itself" 
begin

definition alpha :: "'f \<Rightarrow> 'a mat list \<Rightarrow> 'a mat" ("\<alpha>") where 
  "\<alpha> f mats = (case Alpha (f,length mats) of (cs, c) \<Rightarrow> 
     sum_list_mat (map2 (*) cs mats) + c)" 

definition core_mat_af :: "'f af" where
  "core_mat_af f = (case Alpha f of (cs, c) \<Rightarrow> set (map fst (filter (\<lambda> p. snd p \<noteq> 0\<^sub>m n n) (zip [0 ..< length cs] cs))))" 


interpretation mring: semiring mat_sq_ring by (rule Matrix.semiring_mat)

(* TODO: move sum_list_lpoly to LPoly-theory *)
lemma sum_list_lpoly: assumes "Ball (set ps) (wf_lpoly mat_sq_ring)" 
  and wf_ass: "wf_ass mat_sq_ring \<beta>" 
shows "eval_lpoly mat_sq_ring \<beta> (sum_list_lpoly mat_sq_ring ps) = sum_list_mat (map (\<lambda> p. eval_lpoly mat_sq_ring \<beta> p) ps)" 
  using assms(1)
proof (induct ps)
  case Nil
  show ?case using wf_ass by (simp add: ring_mat_simps)
next
  case (Cons p ps)
  thus ?case using wf_ass unfolding sum_list_lpoly_simps list.simps sum_list_mat_simps
    by (simp add: mring.sum_poly_sound ring_mat_simps)
qed

fun subst_lpoly :: "('w1 \<Rightarrow> ('w2,'a mat)l_poly) \<Rightarrow> ('w1,'a mat)l_poly \<Rightarrow> ('w2,'a mat)l_poly" where
  "subst_lpoly \<sigma> (LPoly c cs) = sum_lpoly mat_sq_ring (sum_list_lpoly mat_sq_ring
    (map (\<lambda> (x,cx). mul_lpoly mat_sq_ring cx (\<sigma> x)) cs)) (c_lpoly c)"

lemma wf_subst_lpoly: assumes "\<forall> x. wf_lpoly mat_sq_ring (\<sigma> x)" 
  and "wf_lpoly mat_sq_ring p" 
shows "wf_lpoly mat_sq_ring (subst_lpoly \<sigma> p)" 
proof (cases p)
  case (LPoly c cs)
  from assms[unfolded this, simplified]
  have *: "c \<in> carrier_mat n n" "snd ` set cs \<subseteq> carrier_mat n n" 
    by (auto simp: ring_mat_simps wf_pvars_def)
  show ?thesis unfolding LPoly subst_lpoly.simps
    unfolding subst_lpoly_def using * assms
    by (fastforce intro!: mring.wf_sum_lpoly mring.wf_sum_list_lpoly mring.wf_mul_lpoly simp: ring_mat_simps
        wf_pvars_def dest!: set_zip_rightD)
qed

lemma eval_subst_lpoly: assumes "\<forall> x. wf_lpoly mat_sq_ring (\<sigma> x)" 
  and "wf_lpoly mat_sq_ring p"
  and beta: "wf_ass mat_sq_ring \<beta>" 
shows "eval_lpoly mat_sq_ring \<beta> (subst_lpoly \<sigma> p) = eval_lpoly mat_sq_ring (\<lambda> x. eval_lpoly mat_sq_ring \<beta> (\<sigma> x)) p" 
proof (cases p)
  case (LPoly c cs)
  from assms[unfolded this, simplified]
  have *: "c \<in> carrier_mat n n" "snd ` set cs \<subseteq> carrier_mat n n" 
    by (auto simp: ring_mat_simps wf_pvars_def)
  from * have c: "wf_lpoly mat_sq_ring (c_lpoly c)" 
    by (auto simp: ring_mat_simps wf_pvars_def)
  {
    fix x
    from assms have "wf_lpoly mat_sq_ring (\<sigma> x)" by auto
    hence "eval_lpoly mat_sq_ring \<beta> (\<sigma> x) \<in> carrier_mat n n" using beta
      by (metis mring.wf_eval_lpoly ring_mat_simps(5))
  }
  hence beta': "wf_ass mat_sq_ring (\<lambda> x. eval_lpoly mat_sq_ring \<beta> (\<sigma> x))" 
    unfolding wf_ass_def by (auto simp add: ring_mat_simps)
  have cc: "eval_lpoly mat_sq_ring \<beta> (c_lpoly c) = c" using beta c
    by auto
  have sum: "sum_list_mat (map (eval_lpoly mat_sq_ring \<beta> \<circ> (\<lambda>(x, cx). mul_lpoly mat_sq_ring cx (\<sigma> x))) cs)
    = eval_pvars mat_sq_ring (\<lambda>x. eval_lpoly mat_sq_ring \<beta> (\<sigma> x)) cs" (is "?P cs")
    using *(2)
  proof (induct cs)
    case Nil
    show ?case by (simp add: ring_mat_simps)
  next
    case (Cons xcx cs)
    then obtain x cx where xcx: "xcx = (x,cx)" by force
    with Cons(2) have cx: "cx \<in> carrier_mat n n" by auto
    from Cons have IH: "?P cs" by force
    show ?case unfolding xcx 
      apply (simp add: ring_mat_simps)
      apply (subst mring.mul_poly_sound[OF beta])
      subgoal using cx by (simp add: ring_mat_simps)
      subgoal using assms by auto
      apply (unfold ring_mat_simps)
      using IH by auto
  qed
  show ?thesis unfolding LPoly subst_lpoly.simps
    apply (subst mring.sum_poly_sound[OF beta _ c])
    subgoal by (rule mring.wf_sum_list_lpoly, insert assms *, 
          auto intro!: mring.wf_mul_lpoly dest: set_zip_rightD simp: ring_mat_simps)
    apply (unfold ring_mat_simps cc)
    apply (subst sum_list_lpoly[OF _ beta])
    subgoal by (insert assms *, auto intro!: mring.wf_mul_lpoly dest: set_zip_rightD simp: ring_mat_simps)
    apply (simp add: ring_mat_simps)
    apply (unfold sum)
    apply (rule comm_add_mat[OF _ *(1)])    
    by (metis \<open>c \<in> carrier mat_sq_ring \<and> wf_pvars mat_sq_ring cs\<close> beta' mring.wf_eval_pvars ring_mat_simps(5))
qed

 
definition alphap :: "'f \<Rightarrow> ('v, 'a mat) l_poly list \<Rightarrow> ('v, 'a mat) l_poly" ("\<alpha>p") where
  "\<alpha>p f lps = (case Alpha (f,length lps) of (cs, c) \<Rightarrow>
     sum_lpoly mat_sq_ring (sum_list_lpoly mat_sq_ring (map2 (mul_lpoly mat_sq_ring) cs lps)) (c_lpoly c))"

abbreviation poly_of where "poly_of t \<equiv> eval_term alphap t (var_lpoly mat_sq_ring)" 

definition inter_lpoly :: "'f \<times> nat \<Rightarrow> (nat, 'a mat)l_poly" where
  "inter_lpoly fk = (case Alpha fk of (cs, c) \<Rightarrow> sum_lpoly mat_sq_ring (sum_list_lpoly mat_sq_ring (map2 (\<lambda> c x. mul_lpoly mat_sq_ring c (var_lpoly mat_sq_ring x)) cs [0..<length cs])) (c_lpoly c))" 

definition "sub_lpoly p q = sum_lpoly mat_sq_ring p (mul_lpoly mat_sq_ring (- 1\<^sub>m n) q)"

fun alpha_lhs_minus_rhs where "alpha_lhs_minus_rhs (l,r) = sub_lpoly (poly_of l) (poly_of r)" 

declare alpha_lhs_minus_rhs.simps[simp del]

lemma wf_sub_lpoly: "wf_lpoly mat_sq_ring p \<Longrightarrow> wf_lpoly mat_sq_ring q \<Longrightarrow> wf_lpoly mat_sq_ring (sub_lpoly p q)" 
  unfolding sub_lpoly_def
  by (intro mring.wf_sum_lpoly, force)
    (intro mring.wf_mul_lpoly, auto simp: ring_mat_simps)

lemma eval_sub_lpoly: assumes p: "wf_lpoly mat_sq_ring p" 
  and q: "wf_lpoly mat_sq_ring q" 
  and beta: "wf_ass mat_sq_ring \<beta>" 
shows "eval_lpoly mat_sq_ring \<beta> (sub_lpoly p q) = eval_lpoly mat_sq_ring \<beta> p - eval_lpoly mat_sq_ring \<beta> q" 
proof -
  have p': "eval_lpoly mat_sq_ring \<beta> p \<in> carrier_mat n n" using p beta 
    by (metis mring.wf_eval_lpoly ring_mat_simps(5))
  have q': "eval_lpoly mat_sq_ring \<beta> q \<in> carrier_mat n n" using q beta 
    by (metis mring.wf_eval_lpoly ring_mat_simps(5))
  show ?thesis
    unfolding sub_lpoly_def
    apply (subst mring.sum_poly_sound[OF beta p])
    subgoal using q by (intro mring.wf_mul_lpoly, auto simp: ring_mat_simps)
    apply (unfold ring_mat_simps)
    apply (subst mring.mul_poly_sound[OF beta _ q])
    subgoal using q by (auto simp: ring_mat_simps)
    apply (unfold ring_mat_simps)
    by (intro eq_matI, insert p' q', auto)
qed

context (* syntactic shape of Alpha is correct + restriction to N for coefficients *)
  assumes Alphapre: "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
begin
lemmas Alpha = Alphapre[rule_format]


lemma wf_poly_of[simp,intro]: "wf_lpoly mat_sq_ring (poly_of t)" 
proof (induct t)
  case (Var x)
  show ?case by (auto intro!: mring.wf_var_lpoly)
next
  case (Fun f ts)
  obtain c cs where Alphaf: "Alpha (f,length ts) = (cs,c)" by force
  from Alpha[OF Alphaf] have *: "set cs \<subseteq> carrier_mat n n" "length cs = length ts" "c \<in> carrier_mat n n" 
    unfolding N_def by auto
  have pc: "wf_lpoly mat_sq_ring (c_lpoly c)" using *(3)
    by (auto simp: wf_pvars_def ring_mat_def)
  show ?case unfolding eval_term.simps 
    unfolding alphap_def[of f "(map poly_of ts)"] length_map Alphaf split
  proof (intro mring.wf_sum_lpoly[OF mring.wf_sum_list_lpoly pc] ballI)
    fix p 
    assume "p \<in> set (map2 (mul_lpoly mat_sq_ring) cs (map poly_of ts))" 
    with *(2) obtain c t where "c \<in> set cs" "t \<in> set ts" and 
      p: "p = mul_lpoly mat_sq_ring c (poly_of t)" 
      by (force simp: set_conv_nth)
    from this(1-2) *(1) Fun have "c \<in> carrier_mat n n" "wf_lpoly mat_sq_ring (poly_of t)" 
      by auto
    from mring.wf_mul_lpoly[OF _ this(2)] this(1)
    show "wf_lpoly mat_sq_ring p" unfolding p by (auto simp: ring_mat_def)
  qed
qed

lemma eval_poly_of: assumes "range \<beta> \<subseteq> carrier_mat n n" 
  shows "eval_term \<alpha> t \<beta> = eval_lpoly mat_sq_ring \<beta> (poly_of t)" 
proof -
  from assms have beta[simp]: "wf_ass mat_sq_ring \<beta>" 
    by (auto simp: wf_ass_def ring_mat_def)
  show ?thesis 
  proof (induct t)
    case (Var x)
    show ?case by simp
  next
    case (Fun f ts)
    obtain c cs where Alphaf: "Alpha (f,length ts) = (cs,c)" by force
    from Alpha[OF Alphaf] have *: "set cs \<subseteq> carrier_mat n n" "length cs = length ts" "c \<in> carrier_mat n n" 
      unfolding N_def by auto
    have c: "wf_lpoly mat_sq_ring (c_lpoly c)" using *
      by (auto simp: ring_mat_simps wf_pvars_def)
    define list where "list = map2 (mul_lpoly mat_sq_ring) cs (map poly_of ts)" 
    {
      fix p
      assume "p \<in> set list" 
      from this[unfolded list_def] *(2) obtain c t where "c \<in> set cs" "t \<in> set ts" and 
        p: "p = mul_lpoly mat_sq_ring c (poly_of t)" 
        by (force simp: set_conv_nth)
      from this(1-2) *(1) have "c \<in> carrier_mat n n" "wf_lpoly mat_sq_ring (poly_of t)" 
        by auto
      from mring.wf_mul_lpoly[OF _ this(2)] this(1)
      have "wf_lpoly mat_sq_ring p" unfolding p by (auto simp: ring_mat_def) 
    } note wf_list = this 
    have cc: "eval_lpoly mat_sq_ring \<beta> (c_lpoly c) = c" using c by (auto simp add: ring_mat_simps)
    {
      fix i
      assume i: "i < length ts" 
      hence "ts ! i \<in> set ts" by auto
      from Fun[OF this]
      have "map2 (*) cs (map (\<lambda>s. \<alpha>\<lbrakk>s\<rbrakk>\<beta>) ts) ! i =
        map (eval_lpoly mat_sq_ring \<beta>) (map2 (mul_lpoly mat_sq_ring) cs (map poly_of ts)) ! i" 
        using * i by (auto simp: o_def , subst mring.mul_poly_sound) (auto simp: ring_mat_simps)
    } note eq = this
    show ?case
      unfolding eval_term.simps alpha_def[of f] alphap_def[of f] length_map Alphaf split
      unfolding list_def[symmetric]
      apply (subst mring.sum_poly_sound[OF _ _ c], force)
      subgoal using wf_list by (intro mring.wf_sum_list_lpoly, auto)
      apply (subst sum_list_lpoly[OF _ beta])
      subgoal using wf_list by auto
      apply (unfold ring_mat_simps list_def cc)
      apply (rule arg_cong[of _ _ "\<lambda> ls. sum_list_mat ls + c"])
      apply (intro nth_equalityI, force)
      subgoal for i using eq * by auto
      done
  qed
qed

lemma wf_inter_lpoly: "wf_lpoly mat_sq_ring (inter_lpoly fk)"
proof -
  obtain f k where fk: "fk = (f,k)" by force
  obtain cs c where Alphaf: "Alpha (f,k) = (cs,c)" by force
  from Alpha[OF Alphaf] have *: "set cs \<subseteq> carrier_mat n n" "length cs = k" "c \<in> carrier_mat n n" 
    by (auto simp: N_def)
  show ?thesis unfolding inter_lpoly_def fk Alphaf split
    apply (intro mring.wf_sum_lpoly mring.wf_sum_list_lpoly ballI) 
    subgoal for p using *
      by (auto intro!: mring.wf_mul_lpoly simp: ring_mat_simps dest: set_zip_leftD)
    subgoal using * by (auto simp: ring_mat_simps wf_pvars_def)
    done
qed

lemma wf_alpha_lhs_minus_rhs: "wf_lpoly mat_sq_ring (alpha_lhs_minus_rhs rule)" 
proof -
  obtain l r where rule: "rule = (l,r)" by force
  show ?thesis unfolding alpha_lhs_minus_rhs.simps rule
    by (intro wf_sub_lpoly wf_poly_of)
qed

lemma eval_alpha_lhs_minus_rhs: assumes "range \<beta> \<subseteq> carrier_mat n n"
  shows "eval_lpoly mat_sq_ring \<beta> (alpha_lhs_minus_rhs (l,r)) = 
    eval_term \<alpha> l \<beta> - eval_term \<alpha> r \<beta>" 
  unfolding eval_poly_of[OF assms] alpha_lhs_minus_rhs.simps
  by (rule eval_sub_lpoly[OF wf_poly_of wf_poly_of], insert assms, auto simp: wf_ass_def ring_mat_simps)

lemma inter_lpoly: assumes D: "D \<noteq> {}" "D \<subseteq> carrier_mat n n" 
  and "\<forall> \<beta>. range \<beta> \<subseteq> D \<longrightarrow> eval_lpoly mat_sq_ring \<beta> (inter_lpoly (f,k)) \<in> D" 
  and "length as = k" and "set as \<subseteq> D" 
shows "\<alpha> f as \<in> D" 
proof -
  obtain cs c where Alphaf: "Alpha (f,k) = (cs,c)" by force
  from Alpha[OF Alphaf] have *: "set cs \<subseteq> carrier_mat n n" "length cs = k" "c \<in> carrier_mat n n" 
    by (auto simp: N_def)
  from D obtain d where d: "d \<in> D" by auto
  define \<beta> where "\<beta> i = (if i < k then as ! i else d)" for i
  from assms d have beta: "range \<beta> \<subseteq> D" unfolding \<beta>_def by auto  
  with assms have inD: "eval_lpoly mat_sq_ring \<beta> (inter_lpoly (f,k)) \<in> D" by auto
  from beta D have beta': "wf_ass mat_sq_ring \<beta>" unfolding wf_ass_def ring_mat_simps 
    by auto
  define list where "list = map2 (\<lambda>x y. mul_lpoly mat_sq_ring x (var_lpoly mat_sq_ring y)) cs [0..<length cs]" 
  have cc: "eval_lpoly mat_sq_ring \<beta> (c_lpoly c) = c" using * by (auto simp add: ring_mat_simps)
  have c: "wf_lpoly mat_sq_ring (c_lpoly c)" using *
    by (auto simp: ring_mat_simps wf_pvars_def)
  {
    fix p
    assume "p \<in> set list" 
    from this[unfolded list_def] *(2) obtain c i where "c \<in> set cs" "i < k" and 
      p: "p = mul_lpoly mat_sq_ring c (var_lpoly mat_sq_ring i)" 
      by (force simp: set_conv_nth)
    from this(1-2) *(1) have "c \<in> carrier_mat n n" "wf_lpoly mat_sq_ring (var_lpoly mat_sq_ring i)" 
      by auto
    from mring.wf_mul_lpoly[OF _ this(2)] this(1)
    have "wf_lpoly mat_sq_ring p" unfolding p by (auto simp: ring_mat_def) 
  } note wf_list = this 
  have "eval_lpoly mat_sq_ring \<beta> (inter_lpoly (f,k)) = \<alpha> f as" 
    unfolding inter_lpoly_def Alphaf split alpha_def assms
    unfolding list_def[symmetric]
    apply (subst mring.sum_poly_sound[OF beta' mring.wf_sum_list_lpoly c])
    subgoal using wf_list by auto
    apply (unfold ring_mat_simps cc)
    apply (rule arg_cong[of _ _ "\<lambda> t. t + _"])
    apply (subst sum_list_lpoly[OF _ beta'])
    subgoal using wf_list by auto
    apply (rule arg_cong[of _ _ sum_list_mat])
    apply (unfold list_def)
    apply (intro nth_equalityI)
    subgoal using * assms by simp
    subgoal for i using assms * beta'
      apply simp
      apply (subst mring.mul_poly_sound[OF beta'])
      by (insert assms, auto simp: ring_mat_simps \<beta>_def set_conv_nth)
    done
  with inD show ?thesis by auto
qed


lemma \<alpha>_append: assumes "Suc (length bef + length aft) = k" 
  and "length bef = i" 
  and "Alpha (f,k) = (cs,c)" 
  and "{a,b} \<union> set bef \<union> set aft \<subseteq> carrier_mat n n" 
shows "\<alpha> f (bef @ a # aft) - \<alpha> f (bef @ b # aft) = cs ! i * (a - b)"
proof -
  from Alpha[OF assms(3)]
  have *: "set cs \<subseteq> N" "length cs = k" "c \<in> carrier_mat n n" by auto
  from * assms have "i < k" by auto

  from * have **: "set cs \<subseteq> carrier_mat n n" unfolding N_def by auto
  have len: "Suc (length bef + length aft) = k" using assms by auto
  define list where "list = (\<lambda> a. map2 (*) cs (bef @ a # aft))" 
  have len': "length (list a) = k" for a unfolding list_def using * assms by auto
  define sum where "sum = (\<lambda> a. sum_list_mat (list a))"
  have list: "a \<in> carrier_mat n n \<Longrightarrow> set (list a) \<subseteq> carrier_mat n n" for a
    unfolding list_def
    apply (insert assms, auto intro!: mult_carrier_mat[of _ n n]) 
    subgoal using ** by (auto dest: set_zip_leftD)
    subgoal by (auto dest!: set_zip_rightD)
    done
  have sum: "a \<in> carrier_mat n n \<Longrightarrow> sum a \<in> carrier_mat n n" for a
    unfolding sum_def using list[of a] 
    by (rule sum_list_mat_carrier)

  have take: "take i (list b) = take i (list a)" unfolding list_def using assms(2) 
    by (intro nth_equalityI, auto simp: nth_append)
  have drop: "drop (Suc i) (list b) = drop (Suc i) (list a)" unfolding list_def using assms(2) *(2) \<open>i < k\<close>
    apply (intro nth_equalityI, force)
    by (auto simp: nth_append len)
  define both where "both = sum_list_mat (take i (list a) @ drop (Suc i) (list a))"
  have both: "both \<in> carrier_mat n n" 
    unfolding both_def
    apply (rule sum_list_mat_carrier)
    apply (rule subset_trans[OF _ list[of a]])    
    subgoal by (simp add: set_drop_subset set_take_subset)
    using assms by auto
  have listi: "list a ! i = cs ! i * a" for a unfolding list_def using * \<open>i < k\<close> assms(2) by auto
  have "cs ! i \<in> N" using * \<open>i < k\<close> assms(2) by auto
  hence csi: "cs ! i \<in> carrier_mat n n" unfolding N_def by auto
  from assms have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" by auto
  from ab csi have listic: "list a ! i \<in> carrier_mat n n" "list b ! i \<in> carrier_mat n n" 
    unfolding listi by auto
  have "\<alpha> f (bef @ a # aft) - \<alpha> f (bef @ b # aft) = sum a + c - (sum b + c)" 
    unfolding alpha_def using len assms(3) split sum_def list_def by simp
  also have "\<dots> = sum a - sum b" using sum[of a] sum[of b] assms * by auto
  also have "\<dots> = list a ! i - list b ! i" 
    unfolding sum_def 
    apply (subst (1 2) sum_list_split[OF list, unfolded len', OF _ \<open>i < k\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    apply (unfold take drop)
    apply (unfold both_def[symmetric])
    using listic both by auto
  also have "\<dots> = cs ! i * (a - b)" unfolding listi using csi ab
    by (simp add: mult_minus_distrib_mat)
  finally show "\<alpha> f (bef @ a # aft) - \<alpha> f (bef @ b # aft) = cs ! i * (a - b)" by auto
qed



context (* generic core interpretation over domain D with (an approximation of a) core C *)
  fixes C D :: "'a mat set" 
begin

definition NS where "NS = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> D \<and> m1 - m2 \<in> N}" 
definition S where "S = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> D \<and> m1 - m2 \<in> C}" 


context (* properties of C and D *)
  assumes delta_pos: "\<delta> > 0"   (* the \<delta>-ordering is strongly normalizing *)
  and DN: "D \<subseteq> N" 
  and CP: "C \<subseteq> P" 
  and NC: "\<And> a b. a \<in> N \<Longrightarrow> b \<in> C \<Longrightarrow> a + b \<in> C" (* N + C \<subseteq> C *)
  and DC: "\<And> a b. a \<in> D \<Longrightarrow> b \<in> C \<Longrightarrow> a * b \<in> C" (* D * C \<subseteq> C, required for strict mono setting *)
begin

lemma Dn: "a \<in> D \<Longrightarrow> a \<in> carrier_mat n n" using DN unfolding N_def by auto
lemma Cn: "a \<in> C \<Longrightarrow> a \<in> carrier_mat n n" using CP unfolding P_def N_def by auto

lemma CN: "C \<subseteq> N" using CP P_in_N by auto

context (* assumption alpha(f) : D^k \<rightarrow> D *)
  assumes \<alpha>Dpre: "\<forall> as f. set as \<subseteq> D \<longrightarrow> \<alpha> f as \<in> D" (* \<alpha> : D\<^sup>k \<rightarrow> D *)
begin
lemmas \<alpha>D = \<alpha>Dpre[rule_format]  

interpretation coreAlgebra: wf_algebra NS S D \<alpha> "typ" 
proof
  {
    fix x y z
    assume *: "(x,y) \<in> NS" "(y,z) \<in> S" 
    hence "x \<in> carrier_mat n n" "y \<in> carrier_mat n n" "z \<in> carrier_mat n n" using Dn 
      by (auto simp: NS_def S_def)
    hence id: "x - z = (x - y) + (y - z)" by auto
    from NC[of "x - y" "y - z", folded id] * 
    have "(x,z) \<in> S" unfolding NS_def S_def by auto
  }
  thus "NS O S \<subseteq> S" by auto
  show "S \<subseteq> NS" unfolding S_def NS_def using CN by auto
  show "refl_on D NS" unfolding NS_def 
    by (intro refl_onI, auto dest: Dn)
  {
    fix x y z
    assume *: "(x,y) \<in> S" "(y,z) \<in> NS" 
    hence "x \<in> carrier_mat n n" "y \<in> carrier_mat n n" "z \<in> carrier_mat n n" using Dn 
      by (auto simp: NS_def S_def)
    hence id: "x - z = (y - z) + (x - y)" by auto
    from NC[of "y - z" "x - y", folded id] * 
    have "(x,z) \<in> S" unfolding NS_def S_def by auto
  }
  thus "S O NS \<subseteq> S" unfolding S_def NS_def by auto
  show "trans_on D NS" 
    unfolding trans_on_def NS_def 
  proof (clarsimp, goal_cases)
    case *: (1 x y z)
    have id: "x - z = (x - y) + (y - z)" using * by (auto dest!: Dn)
    show ?case unfolding id using * by (metis N_add_closed)
  qed
  show "trans_on D S" 
    unfolding trans_on_def S_def 
  proof (clarsimp, goal_cases)
    case *: (1 x y z)
    have id: "x - z = (x - y) + (y - z)" using * by (auto dest!: Dn)
    show ?case unfolding id using * CN
      by (intro NC, auto)
  qed
  note SN = SN_delta[OF delta_pos]
  let ?gt = "(\<lambda>x y. \<delta> \<le> x - y)"  
  have "\<delta> \<ge> 0" 
  proof (rule ccontr)
    let ?rel = "{(x,y) . y \<ge> 0 \<and> x - y \<ge> \<delta>}" 
    assume "\<not> ?thesis" 
    hence "(0,0) \<in> ?rel" by auto
    with SN show False by fast
  qed  
  hence SN: "SN_one_mono_ordered_semiring_1 \<delta> ?gt" 
    apply (unfold_locales)
    subgoal by (metis dual_order.trans plus_right_mono uminus_add_conv_diff)
    subgoal by (smt (verit, best) add_diff_eq diff_add_cancel dual_order.trans plus_right_mono
          uminus_add_conv_diff)
    subgoal by (metis add_increasing diff_add_cancel order_refl order_trans)
    by (insert SN, auto) 
  have "SN S"
    apply (intro SN_subset[OF SN_one_mono_ordered_semiring_1.mat_gt_SN[OF SN le_refl, of n]])
    apply (clarify, intro conjI)
  proof -
    fix a b
    assume "(a, b) \<in> S" 
    from this[unfolded S_def]
    have *: "a \<in> D" "b \<in> D" "a - b \<in> C" by auto
    show a: "a \<in> carrier_mat n n" using * by (auto dest: Dn)
    show b: "b \<in> carrier_mat n n" using * by (auto dest: Dn)
    show "b \<ge>\<^sub>m 0\<^sub>m n n" using *(2) DN unfolding N_def by auto  
    from * have abP: "a - b \<in> P" using CP by auto
    hence "Mat_gt (a - b) (0\<^sub>m n n)" by (auto simp: P_def)
    thus "Mat_gt a b" unfolding mat_gt_def mat_ge_def using a b 
    proof (clarsimp, goal_cases) 
      case (1 i j)
      show ?case by (rule exI[of _ i], insert 1, auto intro: exI[of _ j])
    qed
  qed
  thus "SN_on S D" by fast
  show "\<And>as f. set as \<subseteq> D \<Longrightarrow> \<alpha> f as \<in> D" by (rule \<alpha>D)

  (* weak monotonicity *)
  fix a b bef aft f
  assume *: "a \<in> D" "b \<in> D" "set (bef @ aft) \<subseteq> D" "(a, b) \<in> NS"
  obtain cs c where split: "Alpha (f, Suc (length bef + length aft)) = (cs, c)" by force
  have cs: "cs ! length bef \<in> N" 
    using Alpha[OF split] by auto
  from * have ab: "a - b \<in> N" unfolding NS_def by auto
  have "\<alpha> f (bef @ a # aft) - \<alpha> f (bef @ b # aft) \<in> N" 
    apply (subst \<alpha>_append[OF refl refl split])
    subgoal using * Dn by auto
    subgoal using cs ab by (rule N_mult_closed)
    done
  thus "(\<alpha> f (bef @ a # aft), \<alpha> f (bef @ b # aft)) \<in> NS" 
    unfolding NS_def using * \<alpha>D by auto
qed

lemma coreAlgebra_S_A_def: "coreAlgebra.S_A = { (l,r). \<forall> x. range x \<subseteq> D \<longrightarrow> 
  eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs (l, r)) \<in> C }" 
  unfolding coreAlgebra.S_A_def unfolding S_def
  apply (intro arg_cong[of _ _ Collect] ext)
  apply (intro arg_cong[of _ _ "\<lambda> f. case_prod f _"] ext)
  apply (intro all_cong)
  apply (subst eval_alpha_lhs_minus_rhs)
  by (insert Dn, auto intro: coreAlgebra.eval_A) 

lemma coreAlgebra_redtriple_order: "redtriple_order coreAlgebra.S_A coreAlgebra.NS_A coreAlgebra.NS_A" 
  by (rule coreAlgebra.redtriple_order)

lemma coreAlgebra_NS_A_def: "coreAlgebra.NS_A = { (l,r). \<forall> x. range x \<subseteq> D \<longrightarrow> 
  eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs (l, r)) \<in> N }" 
  unfolding coreAlgebra.NS_A_def unfolding NS_def
  apply (intro arg_cong[of _ _ Collect] ext)
  apply (intro arg_cong[of _ _ "\<lambda> f. case_prod f _"] ext)
  apply (intro all_cong)
  apply (subst eval_alpha_lhs_minus_rhs)
  by (insert Dn, auto intro: coreAlgebra.eval_A) 

lemma core_mat_af: "af_compatible core_mat_af coreAlgebra.NS_A" 
  unfolding af_compatible_def
proof (intro allI)
  fix f bef s t aft
  show "length bef \<in> core_mat_af (f, Suc (length bef + length aft)) \<or>
       (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> coreAlgebra.NS_A"
  proof -
    let ?i = "length bef" 
    let ?n = "Suc (length bef + length aft)" 
    show ?thesis
    proof (cases "?i \<in> core_mat_af (f, ?n)")
      case False
      obtain cs c where alph: "Alpha (f,?n) = (cs,c)" by force
      from Alpha[OF alph] have cs: "set cs \<subseteq> carrier_mat n n" unfolding N_def by auto
      from alph have len: "length cs = ?n" by (simp add: Alpha)
      hence i: "?i < length cs" by auto
      hence "(?i, cs ! ?i) \<in> set (zip [0..<length cs] cs)" 
        by (auto simp: set_zip intro: exI[of _ ?i])
      with False[unfolded core_mat_af_def alph split, simplified]
      have 0: "cs ! ?i = 0\<^sub>m n n" by force
      define bcs where "bcs = take ?i cs" 
      have lbcs: "length bcs = ?i" unfolding bcs_def using i by auto
      define acs where "acs = drop (Suc ?i) cs" 
      from i have cs0: "cs = bcs @ 0\<^sub>m n n # acs" unfolding bcs_def acs_def 0[symmetric]
        by (rule id_take_nth_drop)
      show ?thesis unfolding coreAlgebra.NS_A_def
      proof (intro disjI2, clarify) 
        fix x :: "'v \<Rightarrow> 'a mat" 
        assume "range x \<subseteq> D" 
        from coreAlgebra.eval_A[OF this] 
        have evalD[intro]: "coreAlgebra.eval t x \<in> D" for t by auto
        hence eval[intro]: "coreAlgebra.eval t x \<in> carrier_mat n n" for t using Dn by auto
        define u where "u = Fun f (bef @ s # aft)" 
        define v where "v = Fun f (bef @ t # aft)" 
        {
          fix t
          define ts where "ts = bef @ t # aft" 
          have lts: "length ts = ?n" unfolding ts_def by auto
          define prods where "prods = map2 (*) cs (map (\<lambda>s. coreAlgebra.eval s x) ts)" 
          have prods: "set prods \<subseteq> carrier_mat n n" 
            using cs unfolding prods_def
            by (auto elim!: in_set_zipE intro!: mult_carrier_mat[of _ n n _ n])
          from lts i len have len': "length ts = length cs" "length prods = length cs" 
            unfolding prods_def by auto
          hence i': "?i < length prods" using i by auto
          have "coreAlgebra.eval (Fun f ts) x = sum_list_mat prods + c"
            by (simp add: alpha_def alph lts prods_def)
          also have "\<dots> = prods ! ?i + sum_list_mat (take ?i prods @ drop (Suc ?i) prods) + c" 
            by (subst sum_list_split[OF prods i'], auto)
          also have "prods ! ?i = 0\<^sub>m n n" unfolding prods_def cs0
            unfolding bcs_def ts_def using i eval[of t] by (simp add: nth_append)
          also have "take (length bef) prods = map2 (*) bcs (map (\<lambda>s. coreAlgebra.eval s x) bef)" 
            unfolding prods_def ts_def cs0 using lbcs
            by auto
          also have "drop (Suc (length bef)) prods = map2 (*) acs (map (\<lambda>s. coreAlgebra.eval s x) aft)" 
            unfolding prods_def ts_def cs0 using lbcs
            by auto  
          finally have "coreAlgebra.eval (Fun f ts) x =            
             0\<^sub>m n n +
             sum_list_mat
              (map2 (*) bcs (map (\<lambda>s. coreAlgebra.eval s x) bef) @
               map2 (*) acs (map (\<lambda>s. coreAlgebra.eval s x) aft)) +
             c" 
            by simp
        }
        hence id: "coreAlgebra.eval u x = coreAlgebra.eval v x"
          by (auto simp: u_def v_def)
        show "(coreAlgebra.eval (Fun f (bef @ s # aft)) x,
               coreAlgebra.eval (Fun f (bef @ t # aft)) x) \<in> NS" 
          unfolding NS_def u_def[symmetric] v_def[symmetric] using eval[of v]
          by (clarsimp, intro conjI evalD, simp add: id)
      qed
    qed auto
  qed
qed


lemma ce_compat: assumes Alph: "Alpha = Alpha_list_to_Alpha def fk_cs" 
  and def: "def \<in> C" 
  shows "ce_compatible coreAlgebra.S_A" "ce_compatible coreAlgebra.NS_A" 
proof -
  define M where "M = max_list (map (snd o fst) fk_cs)" 
  show "ce_compatible coreAlgebra.S_A" unfolding ce_compatible_def
  proof (intro exI[of _ M] allI impI)
    fix m c
    assume m: "m \<ge> M" 
    {
      fix s t u :: "('f,'v)term" 
      assume u: "u \<in> {s,t}" 
      define comb where "comb = Fun c (t # s # replicate m (Var undefined))" 
      {
        fix \<beta> :: "'v \<Rightarrow> _" 
        assume beta: "range \<beta> \<subseteq> D" 
        {
          assume "Alpha (c, Suc (Suc m)) \<noteq> default_Alpha def (c, Suc (Suc m))" 
          from this[unfolded Alph Alpha_list_to_Alpha_def]
          have "Suc (Suc m) \<in> set (map (snd o fst) fk_cs)" 
            by (force split: option.splits dest!: map_of_SomeD)
          from max_list[OF this, folded M_def] m have False by auto
        }
        hence Alphac: "Alpha (c, Suc (Suc m)) = default_Alpha def (c, Suc (Suc m))" by auto  
        define v where "v = (if u = s then t else s)" 
        have evalE[simp]: "coreAlgebra.eval t \<beta> \<in> D" for t
          by (meson coreAlgebra.eval_A beta left_mult_one_mat)
        hence evalN: "coreAlgebra.eval t \<beta> \<in> N" for t using DN by auto
        hence evaln[simp]: "coreAlgebra.eval t \<beta> \<in> carrier_mat n n" for t by (auto simp: N_def)
        have [simp]: "\<beta> x \<in> carrier_mat n n" "\<beta> x \<in> N" for x 
          using beta Dn DN by blast+
        have [simp]: "def \<in> carrier_mat n n" using def Cn by auto
        note [simp] = left_mult_one_mat[of _ n n]
        define repl where "repl = sum_list_mat (replicate m (\<beta> undefined))" 
        have replN: "repl \<in> N" unfolding repl_def
          by (intro sum_list_mat_N, auto)
        have [simp]: "repl \<in> carrier_mat n n" using replN unfolding N_def by auto
        define rest where "rest = coreAlgebra.eval v \<beta> + repl + def" 
        have rest: "rest \<in> C" unfolding rest_def using replN evalN[of v] def 
          using N_add_closed NC by presburger
        have restn[simp]: "rest \<in> carrier_mat n n" using rest by (rule Cn)
        note [simp] = assoc_add_mat[of _ n n]
        note comm = comm_add_mat[of _ n n]
        have "coreAlgebra.eval comb \<beta> = coreAlgebra.eval t \<beta> + (coreAlgebra.eval s \<beta> + repl) + def" 
          by (simp add: alpha_def Alphac default_Alpha_def repl_def comb_def)
        also have "\<dots> = (coreAlgebra.eval t \<beta> + coreAlgebra.eval s \<beta>) + repl + def" 
          by simp
        also have "\<dots> = coreAlgebra.eval u \<beta> + coreAlgebra.eval v \<beta> + repl + def" 
          using u unfolding v_def by (cases "u = s", auto simp: comm) 
        also have "\<dots> = coreAlgebra.eval u \<beta> + rest" by (simp add: rest_def)
        also have "\<dots> - coreAlgebra.eval u \<beta> = rest" using evaln[of u] restn
          by (metis add_carrier_mat comm mat_add_eq_minus)
        also have "\<dots> \<in> C" by fact
        finally have "coreAlgebra.eval comb \<beta> - coreAlgebra.eval u \<beta> \<in> C" .
        note this evalE
      }
      hence "(comb, u) \<in> coreAlgebra.S_A" unfolding coreAlgebra.S_A_def unfolding S_def by auto  
    } note main = this  
    show "ce_trs (c,m) \<subseteq> coreAlgebra.S_A" unfolding ce_trs.simps using main by blast
  qed
  thus "ce_compatible coreAlgebra.NS_A" using coreAlgebra.S_A_imp_NS_A unfolding ce_compatible_def
    by blast
qed


context (* demanding strict monotonicity *)
  assumes strictMonoPreM: "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> set cs \<subseteq> D" 
begin

lemmas strictMonoM = strictMonoPreM[rule_format]

interpretation coreAlgebra: mono_wf_algebra NS S D \<alpha> "typ" 
proof
  fix a b bef aft f
  assume *: "a \<in> D" "b \<in> D" "set (bef @ aft) \<subseteq> D" "(a, b) \<in> S"
  obtain cs c where split: "Alpha (f, Suc (length bef + length aft)) = (cs, c)" by force
  have cs: "cs ! length bef \<in> D"
    using strictMonoM[OF split] Alpha[OF split] by auto
  from * have ab: "a - b \<in> C" unfolding S_def by auto
  have "\<alpha> f (bef @ a # aft) - \<alpha> f (bef @ b # aft) \<in> C" 
    apply (subst \<alpha>_append[OF refl refl split])
    subgoal using * Dn by auto
    subgoal using cs ab by (rule DC)
    done
  thus "(\<alpha> f (bef @ a # aft), \<alpha> f (bef @ b # aft)) \<in> S" 
    unfolding S_def using * \<alpha>D by auto
qed

lemma ctxt_closed_S: "ctxt.closed coreAlgebra.S_A" 
  by (simp add: coreAlgebra.S_A_mono one_imp_ctxt_closed)

lemma core_matrix_interpretation_for_TRSs: 
  assumes weak: "\<And> rule x. rule \<in> R2 \<Longrightarrow> range x \<subseteq> D \<Longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N" 
  and strict: "\<And> rule x. rule \<in> R1 \<Longrightarrow> range x \<subseteq> D \<Longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> C"
shows "SN (relto (rstep R1) (rstep R2))" 
proof -
  interpret mono_redtriple_order coreAlgebra.S_A coreAlgebra.NS_A coreAlgebra.NS_A by (rule coreAlgebra.mono_redtriple_order)
  show ?thesis
    by (rule manna_ness_relto; unfold coreAlgebra_NS_A_def coreAlgebra_S_A_def, insert assms, auto)
qed

end (* strictly monotone setting *)
end (* alpha : D^k \<rightarrow> D *)

context (* sufficient criteria to ensure conditions with universal quantification *)
  (* for the conditions, we require more properties on the domain D *)
  assumes CD: "\<And> a b. a \<in> C \<Longrightarrow> b \<in> D \<Longrightarrow> a * b \<in> C" (* C * D \<subseteq> C *)
    and DD: "\<And> a b. a \<in> D \<Longrightarrow> b \<in> D \<Longrightarrow> a * b \<in> D" (* D * D \<subseteq> D *)
    and ND: "\<And> a b. a \<in> N \<Longrightarrow> b \<in> D \<Longrightarrow> a + b \<in> D" (* N + D \<subseteq> D *)
begin

lemma DN': "a \<in> D \<Longrightarrow> b \<in> N \<Longrightarrow> a + b \<in> D" 
  using ND[of b a] Dn[of a] N_el_in_carr[of b] comm_add_mat[of a n n b]
  by auto

lemma ensure_Dk_to_D_local: assumes "Alpha (f,k) = (cs, c)" 
  and "set (c # cs) \<inter> D \<noteq> {}" 
  and cN: "c \<in> N" 
  and las: "length as = k" 
  and asD: "set as \<subseteq> D" 
shows "\<alpha> f as \<in> D" 
proof -
  define prods where "prods = map2 (*) cs as" 
  have id: "\<alpha> f as = sum_list_mat prods + c" 
    unfolding alpha_def assms split prods_def by simp
  from Alpha[OF assms(1)] 
  have csN: "set cs \<subseteq> N" and lcs: "length cs = k" and c: "c \<in> carrier_mat n n" 
    by auto
  from csN N_el_in_carr have cs: "set cs \<subseteq> carrier_mat n n" by auto
  from asD Dn have as: "set as \<subseteq> carrier_mat n n" by auto
  have prodsN: "set prods \<subseteq> N" unfolding prods_def
    using csN DN asD by (auto elim!: in_set_zipE N_mult_closed)
  hence prods: "set prods \<subseteq> carrier_mat n n" unfolding N_def by auto
  show ?thesis
  proof (cases "c \<in> D")
    case True
    have "sum_list_mat prods \<in> N" using prodsN by blast
    from ND[OF this True] show ?thesis unfolding id by auto
  next
    case False
    with assms obtain d where dD: "d \<in> D" and dcs: "d \<in> set cs" by auto
    then obtain i where i: "i < k" and csi: "cs ! i = d" using lcs by (auto simp: set_conv_nth) 
    have lp: "length prods = k" unfolding prods_def using las lcs by auto
    define prodi where "prodi = take i prods @ drop (Suc i) prods" 
    have sub: "set prodi \<subseteq> set prods" unfolding prodi_def by (auto elim: in_set_takeD in_set_dropD)
    have prodiN: "sum_list_mat prodi \<in> N" using prodsN sub by auto
    have id2: "sum_list_mat prods = prods ! i + sum_list_mat prodi" 
      using sum_list_split[OF prods i[folded lp], folded prodi_def] by simp
    have "prods ! i = cs ! i * as ! i" unfolding prods_def using i lcs las by auto
    also have "\<dots> \<in> D" 
      by (intro DD, insert csi dD i las asD, auto)
    finally have "sum_list_mat prods \<in> D" unfolding id2 using prodiN 
      by (rule DN')
    from DN'[OF this cN] show ?thesis unfolding id .
  qed
qed

lemma ensure_Dk_to_D_global: 
  assumes "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> c \<in> N \<and> set (c # cs) \<inter> D \<noteq> {}" 
  shows "\<forall>as f. set as \<subseteq> D \<longrightarrow> \<alpha> f as \<in> D" 
proof (intro allI impI)
  fix as f 
  assume as: "set as \<subseteq> D" 
  let ?k = "length as"
  obtain cs c where alp: "Alpha (f,?k) = (cs,c)" by force
  from assms[rule_format, OF this]
  have "c \<in> N" "set (c # cs) \<inter> D \<noteq> {}" by auto
  from ensure_Dk_to_D_local[OF alp this(2,1) refl as]
  show "\<alpha> f as \<in> D" by auto
qed

lemma eval_lpoly_member_via_N: assumes wf: "wf_lpoly mat_sq_ring p"
  and E: "E \<in> {D, C, N}" 
  and p: "p = LPoly c xcs" 
  and c: "c \<in> E" 
  and xcs: "snd ` set xcs \<subseteq> N" 
  and gam: "range \<gamma> \<subseteq> N"
shows "eval_lpoly mat_sq_ring \<gamma> p \<in> E"
proof -
  from wf[unfolded p, simplified, unfolded wf_pvars_def]
  have c2: "c \<in> carrier_mat n n" and xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
    by (auto simp: ring_mat_def)
  define d where "d = eval_pvars mat_sq_ring \<gamma> xcs" 
  have d: "d \<in> N" unfolding d_def
    using xcs
  proof (induct xcs)
    case Nil
    show ?case by (auto simp: ring_mat_simps)
  next
    case (Cons xa xcs)
    obtain x a where xa: "xa = (x,a)" by force
    from Cons xa have a: "a \<in> N" by force
    from gam have x: "\<gamma> x \<in> N" by auto
    from a x have ax: "a * \<gamma> x \<in> N" by (rule N_mult_closed)
    from Cons xa have IH: "eval_pvars mat_sq_ring \<gamma> xcs \<in> N" by auto
    show ?case unfolding xa eval_pvars.simps ring_mat_simps using ax IH by (rule N_add_closed)
  qed
  have "eval_lpoly mat_sq_ring \<gamma> p = c + d" 
    unfolding p eval_lpoly.simps ring_mat_simps d_def by auto
  also have "c + d \<in> E" 
  proof (cases "E = N")
    case True
    with c d show ?thesis by (auto simp: N_add_closed)
  next
    case False
    with E have "E = D \<or> E = C" by auto
    thus ?thesis
    proof
      assume *: "E = D" 
      from c d show ?thesis unfolding * by (rule DN')
    next
      assume *: "E = C" 
      from c d show ?thesis unfolding * using NC[of d c]
          comm_add_mat[of c n n d] Cn[of c] N_el_in_carr[of d] by auto
    qed
  qed
  finally show "eval_lpoly mat_sq_ring \<gamma> p \<in> E" .
qed

lemma eval_lpoly_member_via_D: assumes wf: "wf_lpoly mat_sq_ring p"
  and E: "E \<in> {C, D, N}" 
  and p: "p = LPoly c xcs" 
  and xcs: "insert c (snd ` set xcs) \<subseteq> N" 
  and inE: "insert c (snd ` set xcs) \<inter> E \<noteq> {}" 
  and gam: "range \<gamma> \<subseteq> D"
shows "eval_lpoly mat_sq_ring \<gamma> p \<in> E"
proof -
  from wf[unfolded p, simplified, unfolded wf_pvars_def]
  have c2: "c \<in> carrier_mat n n" and xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
    by (auto simp: ring_mat_def)
  define d where "d = eval_pvars mat_sq_ring \<gamma> xcs" 
  define prods where "prods = map (\<lambda> (x,c). c * \<gamma> x) xcs"
  have prods: "set prods \<subseteq> carrier_mat n n" using xcs2 gam Dn
    by (fastforce simp: prods_def intro!: mult_carrier_mat[of _ n n])  
  from xcs have xcsn: "snd ` set xcs \<subseteq> carrier_mat n n" unfolding N_def by auto
  have "sum_list_mat prods = eval_pvars mat_sq_ring \<gamma> xcs" unfolding prods_def
  proof (induct xcs)
    case Nil
    show ?case by (auto simp: ring_mat_simps)
  next
    case (Cons xc xcs)
    obtain x c where xc: "xc = (x,c)" by force
    thus ?case using Cons by (auto simp: ring_mat_simps)
  qed
  hence id: "eval_lpoly mat_sq_ring \<gamma> p = c + sum_list_mat prods" 
    unfolding d_def p by (simp add: ring_mat_simps)
  have NE: "\<And> a b. a \<in> N \<Longrightarrow> b \<in> E \<Longrightarrow> a + b \<in> E" 
    using ND NC N_add_closed E by auto
  have En: "E \<subseteq> carrier_mat n n" using E Dn Cn N_def by auto
  have EN: "a \<in> E \<Longrightarrow> b \<in> N \<Longrightarrow> a + b \<in> E" for a b using NE[of b a] 
      N_el_in_carr En comm_add_mat[of a n n b] by auto    
  have ED: "\<And> a b. a \<in> E \<Longrightarrow> b \<in> D \<Longrightarrow> a * b \<in> E"
    using DD N_mult_closed[OF _ set_mp[OF DN]] CD E by auto
  have gamN: "\<gamma> x \<in> N" for x using gam DN by auto
  have prodsN: "set prods \<subseteq> N" unfolding prods_def using xcs gamN
    by (auto intro!: N_mult_closed)

  show ?thesis
  proof (cases "c \<in> E")
    case True
    have "sum_list_mat prods \<in> N" 
      using prodsN by auto
    thus ?thesis unfolding id using EN[OF True] by auto
  next
    case False
    with inE obtain i where "i < length xcs" and inE: "snd (xcs ! i) \<in> E" by (auto simp: set_conv_nth)
    hence i: "i < length prods" unfolding prods_def by auto
    define prodi where "prodi = take i prods @ drop (Suc i) prods" 
    have sub: "set prodi \<subseteq> set prods" unfolding prodi_def by (auto elim: in_set_takeD in_set_dropD)
    have prodiN: "sum_list_mat prodi \<in> N" using prodsN sub by auto
    have id2: "sum_list_mat prods = prods ! i + sum_list_mat prodi" 
      using sum_list_split[OF prods i, folded prodi_def] by simp
    have "prods ! i = snd (xcs ! i) * \<gamma> (fst (xcs ! i))" 
      using i unfolding prods_def by (cases "xcs ! i", auto)
    also have "\<dots> \<in> E" by (intro ED inE, insert gam, auto)
    finally have "sum_list_mat prods \<in> E" unfolding id2 using prodiN EN by auto
    thus ?thesis unfolding id using NE xcs by auto
  qed
qed

theorem core_matrix_interpretation_for_TRSs_sufficient:
  assumes strictMono: "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> set cs \<subseteq> D"
    and suff: "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> c \<in> N \<and> (k = 0 \<longrightarrow> c \<in> D)" 
    and weak: "\<And> rule xcs c. rule \<in> R1 \<union> R2 \<Longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs 
      \<Longrightarrow> insert c (snd ` set xcs) \<subseteq> N"  
    and strict: "\<And> rule xcs c. rule \<in> R1 \<Longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs 
      \<Longrightarrow> insert c (snd ` set xcs) \<inter> C \<noteq> {}"
shows "SN (relto (rstep R1) (rstep R2))" 
proof (rule core_matrix_interpretation_for_TRSs[OF ensure_Dk_to_D_global strictMono])
  show "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> c \<in> N \<and> set (c # cs) \<inter> D \<noteq> {}" 
  proof (intro allI impI conjI)
    fix f k cs c
    assume alp: "Alpha (f, k) = (cs, c)" 
    from suff[rule_format, OF alp] show "c \<in> N" by auto
    show "set (c # cs) \<inter> D \<noteq> {}" 
    proof (cases "k = 0")
      case True
      with suff[rule_format, OF alp] show ?thesis by auto
    next
      case False
      from strictMono[rule_format, OF alp] have "set cs \<subseteq> D" by auto
      moreover from Alpha[OF alp] False have "cs \<noteq> []" by auto
      ultimately show ?thesis by (cases cs, auto)
    qed
  qed
next
  fix rule and x :: "'v \<Rightarrow> 'a mat" 
  assume rule: "rule \<in> R2" and ran: "range x \<subseteq> D"
  obtain c xcs where alp: "alpha_lhs_minus_rhs rule = LPoly c xcs" (is "?e = _") by (cases ?e, auto)
  from weak[OF _ this] rule have inN: "insert c (snd ` set xcs) \<subseteq> N" by auto
  show "eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N"
    by (rule eval_lpoly_member_via_N[OF wf_alpha_lhs_minus_rhs _ alp], insert ran inN DN, auto)
next
  fix rule and x :: "'v \<Rightarrow> 'a mat" 
  assume rule: "rule \<in> R1" and ran: "range x \<subseteq> D"
  obtain c xcs where alp: "alpha_lhs_minus_rhs rule = LPoly c xcs" (is "?e = _") by (cases ?e, auto)
  from weak[OF _ this] rule strict[OF rule this] have inN: "insert c (snd ` set xcs) \<subseteq> N" 
    and inC: "insert c (snd ` set xcs) \<inter> C \<noteq> {}" by auto
  show "eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> C"
    by (rule eval_lpoly_member_via_D[OF wf_alpha_lhs_minus_rhs _ alp], insert ran inN inC DN, auto)
qed
end (* sufficient criteria *)
end (* properties of C and D *)
end (* fixing domain D and approximated core C *)
end (* constraints on interpretation Alpha *)

context (* fixing parameter I *)
  fixes I :: "nat set" 
begin

definition NS\<^sub>E where "NS\<^sub>E = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> E\<^sub>I I \<and> m1 - m2 \<in> N}" 
definition S\<^sub>E where "S\<^sub>E = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> E\<^sub>I I \<and> m1 - m2 \<in> P\<^sub>I I}" 

definition NS\<^sub>M where "NS\<^sub>M = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> M\<^sub>I I \<and> m1 - m2 \<in> N}" 
definition S\<^sub>M where "S\<^sub>M = { (m1,m2) | m1 m2. {m1,m2} \<subseteq> M\<^sub>I I \<and> m1 - m2 \<in> L\<^sub>I I}" 

definition oneE\<^sub>I :: "'a mat" where "oneE\<^sub>I = mat n n (\<lambda> (i,j). if i = j \<and> i \<in> I then 1 else 0)" 

lemma oneE\<^sub>I_mult_oneE\<^sub>I: "oneE\<^sub>I * oneE\<^sub>I = oneE\<^sub>I" 
  apply (intro eq_matI)
    apply (auto simp: oneE\<^sub>I_def scalar_prod_def intro: sum.neutral)
  subgoal for i 
    by (subst sum.remove[of _ i], auto)
  done

lemma oneE\<^sub>I_carrier[simp,intro]: "oneE\<^sub>I \<in> carrier_mat n n" unfolding oneE\<^sub>I_def by auto

fun check_lpoly_generic_EI :: "('a mat \<Rightarrow> bool) \<Rightarrow> ('w, 'a mat) l_poly \<Rightarrow> bool" where
  "check_lpoly_generic_EI cond (LPoly c cs) = (cond (eval_lpoly mat_sq_ring (\<lambda> _. oneE\<^sub>I) (LPoly c cs)) \<and> 
      (\<forall> xci \<in> set cs. snd xci \<ge>\<^sub>m 0\<^sub>m n n))"

definition check_lpoly_EI_N :: "('w, 'a mat) l_poly \<Rightarrow> bool" where
  "check_lpoly_EI_N = check_lpoly_generic_EI (\<lambda> a. a \<ge>\<^sub>m 0\<^sub>m n n)" 

definition check_lpoly_EI_EI :: "('w, 'a mat) l_poly \<Rightarrow> bool" where
  "check_lpoly_EI_EI = check_lpoly_generic_EI (\<lambda> a. a \<ge>\<^sub>m oneE\<^sub>I)" 

definition check_lpoly_EI_PI :: "nat list \<Rightarrow> ('w, 'a mat) l_poly \<Rightarrow> bool" where
  "check_lpoly_EI_PI Il = check_lpoly_generic_EI (\<lambda> a. a \<ge>\<^sub>m 0\<^sub>m n n \<and> (\<exists> i \<in> set Il. \<exists> j \<in> set Il. a $$ (i,j) \<ge> \<delta>))"

context 
  fixes def :: "'a mat"
  assumes def: "def \<in> carrier_mat n n" 
begin
lemma default_Alpha: assumes "default_Alpha def (f,k) = (cs, c)"
  shows "set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
  using assms def unfolding default_Alpha_def
  by auto

lemma Alpha_list_to_Alpha_dim: assumes "Alpha = Alpha_list_to_Alpha def fk_cs" 
  and fk_cs: "\<And> f k cs c. ((f,k),(cs,c)) \<in> set fk_cs \<Longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n"
  and Alpha: "Alpha (f,k) = (cs,c)" 
shows "set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
proof (cases "map_of fk_cs (f,k)")
  case None
  hence "default_Alpha def (f,k) = (cs,c)" using assms unfolding Alpha_list_to_Alpha_def by auto
  from default_Alpha[OF this] show ?thesis by auto
next
  case (Some pair)
  with Alpha have "map_of fk_cs (f,k) = Some (cs,c)" unfolding assms Alpha_list_to_Alpha_def
    by auto
  hence "((f,k),(cs,c)) \<in> set fk_cs" by (rule map_of_SomeD)
  from fk_cs[OF this] show ?thesis .
qed

lemma Alpha_list_to_Alpha_D: assumes "Alpha = Alpha_list_to_Alpha def fk_cs" 
  and one: "1\<^sub>m n \<in> D" 
  and fk_cs: "\<And> f k cs c. ((f,k),(cs,c)) \<in> set fk_cs \<Longrightarrow> set cs \<subseteq> D"
  and Alpha: "Alpha (f,k) = (cs,c)" 
shows "set cs \<subseteq> D" 
proof (cases "map_of fk_cs (f,k)")
  case None
  hence "default_Alpha def (f,k) = (cs,c)" using assms unfolding Alpha_list_to_Alpha_def by auto
  from this[unfolded default_Alpha_def Let_def split] 
  have "set cs \<subseteq> {1\<^sub>m n}" by auto
  with one show ?thesis by auto
next
  case (Some pair)
  with Alpha have "map_of fk_cs (f,k) = Some (cs,c)" unfolding assms Alpha_list_to_Alpha_def
    by auto
  hence "((f,k),(cs,c)) \<in> set fk_cs" by (rule map_of_SomeD)
  from fk_cs[OF this] show ?thesis .
qed

end

context (* conditions on I *)
  assumes I: "I \<noteq> {}" "I \<subseteq> {..<n}" 
begin

lemma one_in_EI: "1\<^sub>m n \<in> E\<^sub>I I" 
  unfolding E\<^sub>I_def using I by auto

lemma one_in_MI: "1\<^sub>m n \<in> M\<^sub>I I" 
  unfolding M\<^sub>I_def using I 
  apply simp
  apply (intro ballI)
  subgoal for i by (intro bexI[of _ i], auto)
  done
  

lemma oneE\<^sub>I: assumes "a \<in> E\<^sub>I I" 
  shows "\<exists> b \<in> N. a = b + oneE\<^sub>I" 
proof (intro bexI)
  from assms have a: "a \<in> carrier_mat n n" by (auto simp: N_def E\<^sub>I_def)
  show "a - oneE\<^sub>I \<in> N" using assms unfolding N_def E\<^sub>I_def 
    by (auto simp: minus_carrier_mat mat_ge_def oneE\<^sub>I_def)
  show "a = a - oneE\<^sub>I + oneE\<^sub>I" using a unfolding oneE\<^sub>I_def
    by auto
qed

lemma E\<^sub>I_N_closed: 
  assumes "a \<in> E\<^sub>I I" "b \<in> N"
  shows "a + b \<in> E\<^sub>I I"
proof -
  from assms have "a + b \<in> N" 
    by (simp add: E\<^sub>I_def N_add_closed)
  moreover
  {
    fix i
    assume i: "i \<in> I" 
    with I have i_n: "i < n" by auto
    hence id: "(a + b) $$ (i, i) = a $$ (i,i) + b $$ (i,i)" using assms
      by (auto simp: N_def E\<^sub>I_def)
    from assms[unfolded E\<^sub>I_def] i have a: "a $$ (i,i) \<ge> 1" by auto
    from assms[unfolded N_def] i_n have b: "b $$ (i,i) \<ge> 0" 
      by (auto simp: mat_ge_def)
    from a b have "1 \<le> (a + b) $$ (i, i)" unfolding id by (metis add_increasing2) 
  }
  ultimately show ?thesis unfolding E\<^sub>I_def
    by auto
qed

lemma N_E\<^sub>I_closed: 
  assumes "a \<in> N" "b \<in> E\<^sub>I I"
  shows "a + b \<in> E\<^sub>I I"
  using E\<^sub>I_N_closed[OF assms(2,1)] assms unfolding N_def E\<^sub>I_def 
  by (metis (no_types, lifting) comm_add_mat mem_Collect_eq)

lemma P\<^sub>I_N_closed: 
  assumes "a \<in> P\<^sub>I I" "b \<in> N"
  shows "a + b \<in> P\<^sub>I I" 
proof -
  from assms have "a + b \<in> N" 
    by (simp add: P\<^sub>I_def N_add_closed)
  moreover 
  from assms(1)[unfolded P\<^sub>I_def] obtain i j where 
    ij: "i \<in> I" "j \<in> I" and a: "a $$ (i,j) \<ge> \<delta>" by auto
  from ij I have ij_n: "i < n" "j < n" by auto
  hence id: "(a + b) $$ (i,j) = a $$ (i,j) + b $$ (i,j)" using assms
    by (auto simp: N_def P\<^sub>I_def)
  from assms[unfolded N_def] ij_n have b: "b $$ (i,j) \<ge> 0" 
    by (auto simp: mat_ge_def)
  from a b have "(a + b) $$ (i,j) \<ge> \<delta>" unfolding id by (metis add_increasing2) 
  ultimately show ?thesis unfolding P\<^sub>I_def using ij
    by auto
qed

lemma N_P\<^sub>I_closed: 
  assumes "a \<in> N" "b \<in> P\<^sub>I I"
  shows "a + b \<in> P\<^sub>I I" 
  using P\<^sub>I_N_closed[OF assms(2,1)] using N_el_in_carr[of a] N_el_in_carr[of b] 
  using assms[unfolded P\<^sub>I_def] comm_add_mat[of a n n b] by auto


(* E\<^sub>I instance *)
lemma E\<^sub>IN: "E\<^sub>I I \<subseteq> N" unfolding E\<^sub>I_def by auto

lemma P\<^sub>IP: "P\<^sub>I I \<subseteq> P" unfolding P\<^sub>I_def P_def
proof (clarsimp simp: N_def mat_gt_def, goal_cases)
  case (1 a i j)
  with I have ij: "i < n" "j < n" by auto
  show ?case 
    apply (rule exI[of _ i])
    apply (rule conjI[OF ij(1) exI[of _ j]])
    using 1 ij by auto
qed

lemma sum_list_mat_0I: assumes "\<And> x. x \<in> set xs \<Longrightarrow> x = 0\<^sub>m n n" 
  shows "sum_list_mat xs = 0\<^sub>m n n" 
  using assms by (induct xs; force)


lemma in_E\<^sub>I_criterion: assumes a: "a \<in> carrier_mat n n"
  and a1: "a \<ge>\<^sub>m oneE\<^sub>I"
shows "a \<in> E\<^sub>I I"
proof -
  {
    fix i j
    assume ij: "i < n" "j < n" 
    with a a1 have a: "a $$ (i,j) \<ge> oneE\<^sub>I $$ (i,j)" unfolding mat_ge_def by auto
    from ij have "oneE\<^sub>I $$ (i,j) \<ge> 0" unfolding oneE\<^sub>I_def by auto
    with a have "a $$ (i,j) \<ge> 0" by auto
  } 
  with a have aN: "a \<in> N" unfolding N_def mat_ge_def by auto
  show ?thesis unfolding E\<^sub>I_def using aN assms I
    unfolding oneE\<^sub>I_def mat_ge_def by auto (smt (verit, best) lessThan_iff subsetD)
qed

lemma oneE\<^sub>I_E\<^sub>I: "oneE\<^sub>I \<in> E\<^sub>I I" 
  by (rule in_E\<^sub>I_criterion, simp, auto simp: mat_ge_def)

lemma decide_lpoly_over_E_in_EPN: assumes wf: "wf_lpoly mat_sq_ring p"
  and p: "p = LPoly c xcs" 
  and EPN: "EPN \<in> {E\<^sub>I I, P\<^sub>I I, N}" 
shows "(\<forall> \<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> EPN) = (snd ` set xcs \<subseteq> N \<and> eval_lpoly mat_sq_ring (\<lambda> _. oneE\<^sub>I) p \<in> EPN)" (is "?quant = ?cond")
proof 
  from wf[unfolded p, simplified, unfolded wf_pvars_def]
  have c2: "c \<in> carrier_mat n n" and xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
    and dist: "distinct (map fst xcs)" 
    by (auto simp: ring_mat_def)
  let ?sum = "\<lambda> \<gamma>. sum_list_mat (map (\<lambda> (x,c). c * \<gamma> x) xcs)" 
  {
    fix \<gamma> :: "'b \<Rightarrow> _" 
    assume gam: "range \<gamma> \<subseteq> N"
    have "eval_lpoly mat_sq_ring \<gamma> p = c + eval_pvars mat_sq_ring \<gamma> xcs" 
      unfolding p eval_lpoly.simps ring_mat_simps by auto
    also have "eval_pvars mat_sq_ring \<gamma> xcs = ?sum \<gamma>" 
      using xcs2 by (induct xcs, auto simp: ring_mat_simps)
    finally have "eval_lpoly mat_sq_ring \<gamma> p = c + ?sum \<gamma>" .
  } note eval = this
  define \<gamma>1 :: "'b \<Rightarrow> 'a mat" where "\<gamma>1 x = oneE\<^sub>I" for x 
  have gam1: "range \<gamma>1 \<subseteq> E\<^sub>I I" unfolding \<gamma>1_def using oneE\<^sub>I_E\<^sub>I by auto  
  from gam1 have gam1n[simp]: "\<gamma>1 x \<in> carrier_mat n n" for x unfolding E\<^sub>I_def N_def by auto
  note mult_carrier[simp,intro!] = mult_carrier_mat[of _ n n _ n, where ?'a = 'a] 
  {
    assume ?quant
    show ?cond
    proof
      from gam1 \<open>?quant\<close> show "eval_lpoly mat_sq_ring (\<lambda> _. oneE\<^sub>I) p \<in> EPN" by (auto simp: \<gamma>1_def)
      show "snd ` set xcs \<subseteq> N" 
      proof
        fix d
        assume "d \<in> snd ` set xcs" 
        then obtain x where "(x,d) \<in> set xcs" by auto
        from split_list[OF this]
        obtain bef aft where xcs: "xcs = bef @ (x,d) # aft" by blast
        from xcs2[unfolded this, of "(x,d)"] 
        have d: "d \<in> carrier_mat n n" by auto
        define B where "B = sum_list_mat (map (\<lambda>(x, c). c * \<gamma>1 x) bef)" 
        define A where "A = sum_list_mat (map (\<lambda>(x, c). c * \<gamma>1 x) aft)" 
        define C where "C = c + (B + A)" 
        define D where "D = C + d * oneE\<^sub>I" 
        have A[simp]: "A \<in> carrier_mat n n" unfolding A_def 
          by (rule sum_list_mat_carrier, insert xcs xcs2 gam1, force)
        have B[simp]: "B \<in> carrier_mat n n" unfolding B_def 
          by (rule sum_list_mat_carrier, insert xcs xcs2 gam1, force)
        have C[simp]: "C \<in> carrier_mat n n" unfolding C_def using c2 by auto
        have D[simp]: "D \<in> carrier_mat n n" unfolding D_def using d C by auto
        {
          fix a'
          assume aN: "a' \<in> N"
          hence a': "a' \<in> carrier_mat n n" unfolding N_def by auto
          define a where "a = oneE\<^sub>I + a'" 
          have aE: "a \<in> E\<^sub>I I" using oneE\<^sub>I_E\<^sub>I aN unfolding a_def by (rule E\<^sub>I_N_closed)
          hence a: "a \<in> carrier_mat n n" using E\<^sub>IN[unfolded N_def] by auto
          define \<gamma> where "\<gamma> = \<gamma>1(x := a)" 
          have gam: "range \<gamma> \<subseteq> E\<^sub>I I" using gam1 aE unfolding \<gamma>_def by auto  
          hence [simp]: "\<gamma> x \<in> carrier_mat n n" for x unfolding E\<^sub>I_def N_def by auto
          from \<open>?quant\<close>[rule_format, OF gam] 
          have "eval_lpoly mat_sq_ring \<gamma> p \<in> N" using EPN
            unfolding E\<^sub>I_def P\<^sub>I_def by auto
          also have "eval_lpoly mat_sq_ring \<gamma> p = c + sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) xcs)" 
            by (rule eval, insert gam, auto simp: E\<^sub>I_def)
          also have "\<dots> = c + (sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) bef) + 
             (d * \<gamma> x + sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) aft)))" using xcs2 d unfolding xcs
            by (simp, subst sum_list_mat_append, force+)
          also have "sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) bef) = B" 
            unfolding B_def 
            by (rule arg_cong[of _ _ sum_list_mat], rule map_cong[OF refl], insert xcs dist,
              auto simp: \<gamma>_def image_iff)
          also have "sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) aft) = A" 
            unfolding A_def 
            by (rule arg_cong[of _ _ sum_list_mat], rule map_cong[OF refl], insert xcs dist,
              auto simp: \<gamma>_def image_iff)
          also have "\<gamma> x = a" unfolding \<gamma>_def by auto
          also have "c + (B + (d * a + A)) = C + d * a" unfolding C_def using a d B A c2
            by (smt (verit, ccfv_SIG) mult_carrier add_carrier_mat assoc_add_mat comm_add_mat)
          also have "\<dots> = D + d * a'" unfolding a_def D_def using C d a'
            by (smt (verit, best) assoc_add_mat mult_add_distrib_mat mult_carrier_mat oneE\<^sub>I_carrier)
          finally have "D + d * a' \<in> N" by auto
        }
        hence in_N: "\<And> a. a \<in> N \<Longrightarrow> D + d * a \<in> N" .
        show "d \<in> N" 
        proof (rule ccontr)
          assume "d \<notin> N" 
          with d obtain i j where ij: "i < n" "j < n" and neg: "d $$ (i,j) < 0" 
            unfolding N_def mat_ge_def by auto
          define neg where "neg = d $$ (i,j)" 
          have neg: "neg < 0" using neg unfolding neg_def by auto
          have i0: "i < n" "0 < n" using ij by auto
          {
            fix x :: 'a
            assume x: "x \<ge> 0" 
            define a where "a = mat n n (\<lambda> ij. if ij = (j,0) then x else 0)" 
            have a: "a \<in> N" "a \<in> carrier_mat n n" unfolding N_def a_def using x by auto
            from in_N[OF this(1)] have addN: "D + d * a \<in> N" .
            with ij have "(D + d * a) $$ (i,0) \<ge> 0" unfolding N_def mat_ge_def
              using N_compo_greater_eq_zero addN by force
            also have "(D + d * a) $$ (i,0) = D $$ (i,0) + (d * a) $$ (i,0)" 
              using d a(2) D ij by auto
            also have "(d * a) $$ (i,0) = neg * x" unfolding neg_def
              apply (subst mat_mult_compo_alt[OF d a(2) i0])
              apply (subst sum.remove[of _ j])
              subgoal by auto
              subgoal using ij by auto
              apply (subst sum.neutral)
              using ij by (auto simp: a_def)
            finally have "- D $$ (i, 0) \<le> neg * x"
              by (metis add_minus_cancel le_add_same_cancel1)
          }
          then obtain c where "\<forall> x \<ge> 0. neg * x \<ge> c" by blast
          from mult_nonneg_imp_neg[OF this] have "neg \<ge> 0" by auto 
          with neg show False by auto
        qed
      qed
    qed
  }
  {
    assume ?cond
    show ?quant
    proof (intro allI impI)
      fix \<gamma> :: "'b \<Rightarrow> 'a mat" 
      assume gam: "range \<gamma> \<subseteq> E\<^sub>I I"
      {
        fix x 
        have "\<gamma> x \<in> E\<^sub>I I" using gam by auto
        from oneE\<^sub>I[OF this] have "\<exists>b\<in>N. \<gamma> x = b + oneE\<^sub>I" .
      }
      hence "\<forall> x. \<exists> b. b \<in> N \<and> \<gamma> x = b + oneE\<^sub>I" by auto
      from choice[OF this] obtain \<beta> where beta: "\<And> x. \<beta> x \<in> N" "\<And> x. \<gamma> x = \<beta> x + oneE\<^sub>I" by auto
      hence betaN[simp]: "\<beta> x \<in> carrier_mat n n" for x unfolding N_def by auto
      from gam have gamN: "range \<gamma> \<subseteq> N" unfolding E\<^sub>I_def by auto
      define A where "A = sum_list_mat (map (\<lambda>(x, c). c * \<beta> x) xcs)" 
      define B where "B = sum_list_mat (map (\<lambda>(x, c). c * \<gamma>1 x) xcs)" 
      have A[simp]: "A \<in> carrier_mat n n" unfolding A_def
        by (rule sum_list_mat_carrier, insert xcs2, force)
      have B[simp]: "B \<in> carrier_mat n n" unfolding B_def
        by (rule sum_list_mat_carrier, insert xcs2, force)
      have "eval_lpoly mat_sq_ring \<gamma> p = c + sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) xcs)" 
        unfolding eval[OF gamN] by simp
      also have "sum_list_mat (map (\<lambda>(x, c). c * \<gamma> x) xcs) = 
        sum_list_mat (map (\<lambda>(x, c). c * \<beta> x + c * \<gamma>1 x) xcs)" 
        apply (rule arg_cong[of _ _ sum_list_mat], rule map_cong[OF refl],
          insert xcs2, auto simp: beta \<gamma>1_def) 
        by (meson betaN mult_add_distrib_mat oneE\<^sub>I_carrier)
      also have "\<dots> = B + A" unfolding B_def A_def
        using xcs2
      proof (induct xcs)
        case (Cons xc xcs)
        obtain x c where xc: "xc = (x,c)" by force
        with Cons(2) have c[simp]: "c \<in> carrier_mat n n" by force
        define A where "A = sum_list_mat (map (\<lambda>(x, c). c * \<beta> x) xcs)" 
        define B where "B = sum_list_mat (map (\<lambda>(x, c). c * \<gamma>1 x) xcs)" 
        have A[simp]: "A \<in> carrier_mat n n" unfolding A_def
          by (rule sum_list_mat_carrier, insert Cons(2), force)
        have B[simp]: "B \<in> carrier_mat n n" unfolding B_def
          by (rule sum_list_mat_carrier, insert Cons(2), force)
        show ?case unfolding xc 
          apply simp
          apply (subst Cons(1))
          subgoal using Cons(2) by auto
          apply (unfold A_def[symmetric])
          apply (unfold B_def[symmetric])  
          by (smt (verit, ccfv_SIG) A B mult_carrier gam1n add_carrier_mat assoc_add_mat betaN c comm_add_mat)
      qed simp
      also have "c + (B + A) = A + (c + B)" using A B c2
        by (metis assoc_add_mat comm_add_mat)
      also have "c + B = eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p" using gam1 unfolding B_def \<gamma>1_def 
        by (subst eval, auto simp: E\<^sub>I_def)
      finally have calc: "eval_lpoly mat_sq_ring \<gamma> p = A + eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p" .
      have AN: "A \<in> N" unfolding A_def using beta(1) \<open>?cond\<close>
        by (intro sum_list_mat_N, auto intro!: N_mult_closed)
      have const: "eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p \<in> EPN" using \<open>?cond\<close> by auto
      show "eval_lpoly mat_sq_ring \<gamma> p \<in> EPN" using const AN EPN
        unfolding calc using N_P\<^sub>I_closed[OF AN] N_add_closed[OF AN] N_E\<^sub>I_closed[OF AN]
        by auto
    qed
  }
qed 


lemma decide_lpoly_over_N_in_EPN: assumes wf: "wf_lpoly mat_sq_ring p"
  and p: "p = LPoly c xcs" 
  and EPN: "EPN \<in> {E\<^sub>I I, P\<^sub>I I, N}" 
shows "(\<forall> \<gamma>. range \<gamma> \<subseteq> N \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> EPN) = (snd ` set xcs \<subseteq> N \<and> c \<in> EPN)" (is "?quant = ?cond")
proof 
  from wf[unfolded p, simplified, unfolded wf_pvars_def]
  have c2: "c \<in> carrier_mat n n" and xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
    and dist: "distinct (map fst xcs)" 
    by (auto simp: ring_mat_def)
  let ?sum = "\<lambda> \<gamma>. sum_list_mat (map (\<lambda> (x,c). c * \<gamma> x) xcs)" 
  {
    fix \<gamma> :: "'b \<Rightarrow> _" 
    assume gam: "range \<gamma> \<subseteq> N"
    have "eval_lpoly mat_sq_ring \<gamma> p = c + eval_pvars mat_sq_ring \<gamma> xcs" 
      unfolding p eval_lpoly.simps ring_mat_simps by auto
    also have "eval_pvars mat_sq_ring \<gamma> xcs = ?sum \<gamma>" 
      using xcs2 by (induct xcs, auto simp: ring_mat_simps)
    finally have "eval_lpoly mat_sq_ring \<gamma> p = c + ?sum \<gamma>" .
  } note eval = this
  {
    assume ?cond
    hence c: "c \<in> EPN" by auto
    show ?quant
    proof (intro allI impI)
      fix \<gamma> :: "'b \<Rightarrow> _" 
      assume gam: "range \<gamma> \<subseteq> N" 
      have sumN: "?sum \<gamma> \<in> N" 
        by (intro sum_list_mat_N, insert gam \<open>?cond\<close>, auto intro!: N_mult_closed)
      show "eval_lpoly mat_sq_ring \<gamma> p \<in> EPN" 
        unfolding eval[OF gam] 
        using E\<^sub>I_N_closed[OF _ sumN] N_add_closed[OF _ sumN] P\<^sub>I_N_closed[OF _ sumN]
        using c EPN by blast
    qed
  }
  {
    assume ?quant
    show ?cond
    proof (intro conjI)
      define \<gamma>0 :: "'b \<Rightarrow> 'a mat" where "\<gamma>0 x = 0\<^sub>m n n" for x 
      have gam0: "range \<gamma>0 \<subseteq> N" unfolding \<gamma>0_def by auto
      with \<open>?quant\<close> have "eval_lpoly mat_sq_ring \<gamma>0 p \<in> EPN" by auto
      with eval[OF gam0] have "c + ?sum \<gamma>0 \<in> EPN" by auto
      also have "?sum \<gamma>0 = 0\<^sub>m n n" unfolding \<gamma>0_def
        using xcs2 by (induct xcs; force)
      finally show "c \<in> EPN" using c2 by auto
      from \<open>?quant\<close>
      have "\<forall>\<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> EPN" 
        unfolding E\<^sub>I_def by auto
      with decide_lpoly_over_E_in_EPN[OF assms(1-3)]
      show "snd ` set xcs \<subseteq> N" by auto
    qed
  }
qed

context
  assumes delta_pos: "\<delta> > 0" 
begin

lemma delta0: "\<delta> \<ge> 0" using delta_pos by auto

lemma EI_PI_mult: assumes "a \<in> E\<^sub>I I" "b \<in> P\<^sub>I I" 
  shows "a * b \<in> P\<^sub>I I" 
proof -
  from assms[unfolded P\<^sub>I_def] 
  obtain i j where ij: "i \<in> I" "j \<in> I" and bN: "b \<in> N" and delt: "\<delta> \<le> b $$ (i, j)" by auto
  from assms[unfolded E\<^sub>I_def] ij have aN: "a \<in> N" and aii: "1 \<le> a $$ (i,i)" by auto  
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding P\<^sub>I_def
  proof (clarify, intro conjI abN, rule bexI[OF _ ij(1)], rule bexI[OF _ ij(2)])
    from ij I have ij: "i < n" "j < n" by auto
    have "(a * b) $$ (i, j) = (\<Sum>k \<in> {..<n}. a $$ (i, k) * b $$ (k, j))" 
      by (subst mat_mult_compo_alt[OF ab ij], auto)
    also have "\<dots> = a $$ (i, i) * b $$ (i, j) + (\<Sum>k \<in> {..<n} - {i}. a $$ (i, k) * b $$ (k, j))" 
      by (subst sum.remove[of _ i], insert ij, auto)
    also have "\<dots> \<ge> 1 * \<delta> + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg aii delta0 delt)
      by (insert aN bN ij, auto simp: N_def)
    finally show "\<delta> \<le> (a * b) $$ (i, j) - 0" by simp
  qed
qed

lemma PI_EI_mult: assumes "a \<in> P\<^sub>I I" "b \<in> E\<^sub>I I" 
  shows "a * b \<in> P\<^sub>I I" 
proof -
  from assms[unfolded P\<^sub>I_def] 
  obtain i j where ij: "i \<in> I" "j \<in> I" and aN: "a \<in> N" and delt: "\<delta> \<le> a $$ (i, j)" by auto
  from assms[unfolded E\<^sub>I_def] ij have bN: "b \<in> N" and bjj: "1 \<le> b $$ (j,j)" by auto  
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding P\<^sub>I_def
  proof (clarify, intro conjI abN, rule bexI[OF _ ij(1)], rule bexI[OF _ ij(2)])
    from ij I have ij: "i < n" "j < n" by auto
    have "(a * b) $$ (i, j) = (\<Sum>k \<in> {..<n}. a $$ (i, k) * b $$ (k, j))" 
      by (subst mat_mult_compo_alt[OF ab ij], auto)
    also have "\<dots> = a $$ (i, j) * b $$ (j, j) + (\<Sum>k \<in> {..<n} - {j}. a $$ (i, k) * b $$ (k, j))" 
      by (subst sum.remove[of _ j], insert ij, auto)
    also have "\<dots> \<ge> \<delta> * 1 + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg bjj delta0 delt)
      by (insert aN bN ij, auto simp: N_def)
    finally show "\<delta> \<le> (a * b) $$ (i, j) - 0" by simp
  qed
qed

lemma EI_EI_mult: assumes "a \<in> E\<^sub>I I" "b \<in> E\<^sub>I I" 
  shows "a * b \<in> E\<^sub>I I" 
proof -
  from assms[unfolded E\<^sub>I_def] have aN: "a \<in> N" by auto
  from assms[unfolded E\<^sub>I_def] have bN: "b \<in> N" by auto  
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding E\<^sub>I_def
  proof (clarify, intro conjI abN, intro ballI)
    fix i
    assume i: "i \<in> I" 
    with I have iN: "i < n" by auto
    from assms[unfolded E\<^sub>I_def] i have ge: "a $$ (i,i) \<ge> 1" "b $$ (i,i) \<ge> 1" by auto
    have "(a * b) $$ (i, i) = (\<Sum>k \<in> {..<n}. a $$ (i, k) * b $$ (k, i))" 
      by (subst mat_mult_compo_alt[OF ab iN iN], auto)
    also have "\<dots> = a $$ (i, i) * b $$ (i, i) + (\<Sum>k \<in> {..<n} - {i}. a $$ (i, k) * b $$ (k, i))" 
      by (subst sum.remove[of _ i], insert iN, auto)
    also have "\<dots> \<ge> 1 * 1 + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg ge delta0)
      by (insert aN bN iN, auto simp: N_def)
    finally show "1 \<le> (a * b) $$ (i, i)" by simp
  qed
qed

lemma N_EI_add: assumes "a \<in> N" "b \<in> E\<^sub>I I" 
  shows "a + b \<in> E\<^sub>I I" 
proof -
  have aN: "a \<in> N" by fact
  from assms[unfolded E\<^sub>I_def] have bN: "b \<in> N" by auto  
  from aN bN have abN: "a + b \<in> N" by (rule N_add_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding E\<^sub>I_def
  proof (clarify, intro conjI abN, intro ballI)
    fix i
    assume i: "i \<in> I" 
    with I have iN: "i < n" by auto
    from assms[unfolded E\<^sub>I_def N_def] i iN have ge: "a $$ (i,i) \<ge> 0" "b $$ (i,i) \<ge> 1" by auto
    have "(a + b) $$ (i, i) = a $$ (i,i) + b $$ (i,i)" 
      using ab iN by auto
    also have "\<dots> \<ge> 0 + 1" using ge by (intro add_mono, auto)
    finally show "1 \<le> (a + b) $$ (i, i)" by simp
  qed
qed

theorem core_matrix_interpretation_for_TRSs_EI: fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> E\<^sub>I I \<and> length cs = k \<and> c \<in> carrier_mat n n" 
    "\<forall>as f. set as \<subseteq> E\<^sub>I I \<longrightarrow> \<alpha> f as \<in> E\<^sub>I I" 
    "\<forall> rule x. rule \<in> R2 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N"
    "\<forall> rule x. rule \<in> R1 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> P\<^sub>I I"
  shows "SN (relto (rstep R1) (rstep R2))"
  by (rule core_matrix_interpretation_for_TRSs[OF _ delta_pos E\<^sub>IN P\<^sub>IP N_P\<^sub>I_closed EI_PI_mult],
      insert assms, fastforce intro!: set_mp[OF E\<^sub>IN], auto)

(* we show that the rule 
   h(a(Y),f(X,Y),Y) \<rightarrow> f(h(h(a(Y),a(Y),Y),f(X,Y),Y),Y)
   cannot be oriented weakly by an E-I interpretation.
   (and we have another proof where we show that this rule can be strictly oriented by 
    some M-I interpretation) 
*)
theorem core_matrix_interpretation_for_TRSs_EI_cannot_solve_example_rule: 
  fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> E\<^sub>I I \<and> length cs = k \<and> c \<in> carrier_mat n n" 
    "\<forall>as f. set as \<subseteq> E\<^sub>I I \<longrightarrow> \<alpha> f as \<in> E\<^sub>I I" 
    "\<forall> rule x. rule \<in> R2 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N"
    "\<forall> rule x. rule \<in> R1 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> P\<^sub>I I"
    and XY: "X \<noteq> Y" 
    and rule: "(Fun h [Fun a [Var Y], Fun f [Var X, Var Y], Var Y], 
    Fun f [Fun h [Fun h [Fun a [Var Y], Fun a [Var Y], Var Y], Fun f [Var X, Var Y], Var Y], Var Y]) 
    \<in> R1 \<union> R2" (is "(?lhs,?rhs) \<in> _")
  shows False
proof -
  from I obtain i where i: "i < n" "i \<in> I" by auto
  have "\<not> 1 \<le> (0 :: 'a)"
    by (simp add: linorder_not_le)
  hence zE: "0\<^sub>m n n \<notin> E\<^sub>I I" unfolding E\<^sub>I_def using i by (auto intro!: bexI[of _ i])

  have EI_EI_add: "x \<in> E\<^sub>I I \<Longrightarrow> y \<in> E\<^sub>I I \<Longrightarrow> x + y \<in> E\<^sub>I I" for x y 
    using N_EI_add[of x y] using E\<^sub>IN by auto

  note Al = assms(1)[rule_format]
  obtain fs f0 where Af: "Alpha (f, Suc (Suc 0)) = (fs,f0)" by force
  note Alf = Al[OF Af] 
  then obtain f1 f2 where fs: "fs = [f1,f2]" by (cases fs; cases "tl fs"; auto)
  note Af = Af[unfolded fs]
  from Alf[unfolded fs] E\<^sub>IN[unfolded N_def]
  have f: "f0 \<in> carrier_mat n n"
    "f1 \<in> carrier_mat n n"
    "f2 \<in> carrier_mat n n"
    and fE: "{f1,f2} \<subseteq> E\<^sub>I I" by auto
  hence fz: "f1 \<noteq> 0\<^sub>m n n" "f2 \<noteq> 0\<^sub>m n n" using zE by auto

  obtain hs h0 where Ah: "Alpha (h, Suc (Suc (Suc 0))) = (hs,h0)" by force
  note Alh = Al[OF Ah] 
  then obtain h1 h2 h3 where hs: "hs = [h1,h2,h3]" by (cases hs; cases "tl hs"; cases "tl (tl hs)", auto)
  note Ah = Ah[unfolded hs]
  from Alh[unfolded hs] E\<^sub>IN[unfolded N_def]
  have h: "h0 \<in> carrier_mat n n"
    "h1 \<in> carrier_mat n n"
    "h2 \<in> carrier_mat n n" 
    "h3 \<in> carrier_mat n n" 
    and hE: "{h1,h2,h3} \<subseteq> E\<^sub>I I" by auto
  hence hz: "h1 \<noteq> 0\<^sub>m n n" "h2 \<noteq> 0\<^sub>m n n" "h3 \<noteq> 0\<^sub>m n n" using zE by auto

  obtain as a0 where Aa: "Alpha (a, Suc 0) = (as,a0)" by force
  note Ala = Al[OF Aa] 
  then obtain a1 where as: "as = [a1]" by (cases as, auto)
  note Aa = Aa[unfolded as]
  note [simp] = right_mult_zero_mat[of _ n n] 
  note [simp] = right_mult_one_mat[of _ n n]
  from Ala[unfolded as] E\<^sub>IN[unfolded N_def]
  have a: "a0 \<in> carrier_mat n n" "a1 \<in> carrier_mat n n" 
    and aE: "{a1} \<subseteq> E\<^sub>I I" by auto
  hence az: "a1 \<noteq> 0\<^sub>m n n" using zE by auto

  note [simp] = mult_carrier_mat[of _ n n _ n] 
  note [simp] = minus_carrier_mat[of _ n n]
  note [simp] = add_carrier_mat[of _ n n]
  note [simp] = uminus_carrier_mat[of _ n n]

  define h1a1 where "h1a1 = h1 * a1" 
  have h1a1E: "h1a1 \<in> E\<^sub>I I" using hE aE unfolding h1a1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have h1a1: "h1a1 \<in> carrier_mat n n" "h1a1 \<noteq> 0\<^sub>m n n" by auto

  define h2a1 where "h2a1 = h2 * a1" 
  have h2a1E: "h2a1 \<in> E\<^sub>I I" using hE aE unfolding h2a1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have h2a1: "h2a1 \<in> carrier_mat n n" "h2a1 \<noteq> 0\<^sub>m n n" by auto

  define h2f1 where "h2f1 = h2 * f1" 
  have h2f1E: "h2f1 \<in> E\<^sub>I I" using hE fE aE unfolding h2f1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have h2f1: "h2f1 \<in> carrier_mat n n" "h2f1 \<noteq> 0\<^sub>m n n" by auto

  define f1h2f1 where "f1h2f1 = f1 * h2f1" 
  have f1h2f1E: "f1h2f1 \<in> E\<^sub>I I" using fE h2f1E unfolding f1h2f1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have f1h2f1: "f1h2f1 \<in> carrier_mat n n" "f1h2f1 \<noteq> 0\<^sub>m n n" by auto

  define h2f2 where "h2f2 = h2 * f2" 
  have h2f2E: "h2f2 \<in> E\<^sub>I I" using hE fE aE unfolding h2f2_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have h2f2: "h2f2 \<in> carrier_mat n n" "h2f2 \<noteq> 0\<^sub>m n n" by auto

  define h2a1_h3 where "h2a1_h3 = h2a1 + h3" 
  have h2a1_h3E: "h2a1_h3 \<in> E\<^sub>I I" using h2a1E hE unfolding h2a1_h3_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have h2a1_h3: "h2a1_h3 \<in> carrier_mat n n" "h2a1_h3 \<noteq> 0\<^sub>m n n" by auto

  define h2f2_h3 where "h2f2_h3 = h2f2 + h3" 
  have h2f2_h3E: "h2f2_h3 \<in> E\<^sub>I I" using h2f2E hE unfolding h2f2_h3_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have h2f2_h3: "h2f2_h3 \<in> carrier_mat n n" "h2f2_h3 \<noteq> 0\<^sub>m n n" by auto

  define h1a1_h2a1_h3 where "h1a1_h2a1_h3 = h1a1 + h2a1_h3"
  have h1a1_h2a1_h3E: "h1a1_h2a1_h3 \<in> E\<^sub>I I" using h2a1_h3E h1a1E unfolding h1a1_h2a1_h3_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have h1a1_h2a1_h3: "h1a1_h2a1_h3 \<in> carrier_mat n n" "h1a1_h2a1_h3 \<noteq> 0\<^sub>m n n" by auto

  define h1a1_h2f2_h3 where "h1a1_h2f2_h3 = h1a1 + h2f2_h3"
  have h1a1_h2f2_h3E: "h1a1_h2f2_h3 \<in> E\<^sub>I I" using h2f2_h3E h1a1E unfolding h1a1_h2f2_h3_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have h1a1_h2f2_h3: "h1a1_h2f2_h3 \<in> carrier_mat n n" "h1a1_h2f2_h3 \<noteq> 0\<^sub>m n n" by auto

  define h1_h1a1_h2a1_h3 where "h1_h1a1_h2a1_h3 = h1 * h1a1_h2a1_h3"
  have h1_h1a1_h2a1_h3E: "h1_h1a1_h2a1_h3 \<in> E\<^sub>I I" using h1a1_h2a1_h3E hE unfolding h1_h1a1_h2a1_h3_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have h1_h1a1_h2a1_h3: "h1_h1a1_h2a1_h3 \<in> carrier_mat n n" "h1_h1a1_h2a1_h3 \<noteq> 0\<^sub>m n n" by auto

  define m1 where "m1 = h1_h1a1_h2a1_h3 + h2f2_h3" 
  have m1E: "m1 \<in> E\<^sub>I I" using h1_h1a1_h2a1_h3E h2f2_h3E unfolding m1_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have m1: "m1 \<in> carrier_mat n n" "m1 \<noteq> 0\<^sub>m n n" by auto

  define f1m1 where "f1m1 = f1 * m1" 
  have f1m1E: "f1m1 \<in> E\<^sub>I I" using fE m1E unfolding f1m1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have f1m1: "f1m1 \<in> carrier_mat n n" "f1m1 \<noteq> 0\<^sub>m n n" by auto

  define f1h1 where "f1h1 = f1 * h1" 
  have f1h1E: "f1h1 \<in> E\<^sub>I I" using fE hE unfolding f1h1_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have f1h1: "f1h1 \<in> carrier_mat n n" "f1h1 \<noteq> 0\<^sub>m n n" by auto

  define f1m1_f2 where "f1m1_f2 = f1m1 + f2" 
  have f1m1_f2E: "f1m1_f2 \<in> E\<^sub>I I" using fE f1m1E unfolding f1m1_f2_def using EI_EI_add by auto
  with E\<^sub>IN[unfolded N_def] zE have f1m1_f2: "f1m1_f2 \<in> carrier_mat n n" "f1m1_f2 \<noteq> 0\<^sub>m n n" by auto


  have lhs: "poly_of ?lhs = LPoly (h1 * a0 + h2 * f0 + h0) [(Y, h1a1_h2f2_h3), (X, h2f1)]"
    by (simp add: alphap_def Ah Af Aa ring_mat_simps var_lpoly_def a f h fz az hz XY 
        h1a1_def[symmetric] h1a1
        h2f1_def[symmetric] h2f1
        h2f2_def[symmetric] h2f2
        h2f2_h3_def[symmetric] h2f2_h3
        h1a1_h2f2_h3_def[symmetric] h1a1_h2f2_h3
        )

  have rhs: "poly_of ?rhs = LPoly (f1 * (h1 * (h1 * a0 + h2 * a0 + h0) + h2 * f0 + h0) + f0) 
     [(Y, f1m1_f2), (X, f1h2f1)]"
    by (simp add: alphap_def Ah Af Aa ring_mat_simps var_lpoly_def a f h fz az hz XY 
        h1a1_def[symmetric] h1a1
        h2a1_def[symmetric] h2a1
        h2f1_def[symmetric] h2f1
        h2f2_def[symmetric] h2f2
        h2f2_h3_def[symmetric] h2f2_h3
        h2a1_h3_def[symmetric] h2a1_h3
        h1a1_h2a1_h3_def[symmetric] h1a1_h2a1_h3
        h1_h1a1_h2a1_h3_def[symmetric] h1_h1a1_h2a1_h3
        m1_def[symmetric] m1
        f1h2f1_def[symmetric] f1h2f1
        f1m1_def[symmetric] f1m1
        f1m1_f2_def[symmetric] f1m1_f2
        )

  define rule where "rule = (?lhs,?rhs)" 
  from assms(3,4,6)[unfolded P\<^sub>I_def, folded rule_def] 
  have inN: "\<forall> x. range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N" 
    by blast
  from wf_alpha_lhs_minus_rhs[of rule] assms(1)
  have wf_alpha: "wf_lpoly mat_sq_ring (alpha_lhs_minus_rhs rule)" 
    unfolding E\<^sub>I_def N_def by force

  define mc where "mc = h1 * a0 + h2 * f0 + h0 +
       - 1\<^sub>m n * (f1 * (h1 * (h1 * a0 + h2 * a0 + h0) + h2 * f0 + h0) + f0)" 
  define m3 where "m3 = h1a1_h2f2_h3 + - f1m1_f2" 
  define m4 where "m4 = h2f1 + - f1h2f1" 
  define m5 where "m5 = f1h1 * h2a1_h3 + f2" 
  define rem where "rem = (if m4 = 0\<^sub>m n n then [] else [(X,m4)])" 
  have rem: "rem = [] \<or> rem = [(X,m4)]" unfolding rem_def by auto

  have m5E: "m5 \<in> E\<^sub>I I" unfolding m5_def using f1h1E h2a1_h3E fE
    by (intro EI_EI_mult EI_EI_add, auto)
  hence m5: "m5 \<in> carrier_mat n n" using E\<^sub>IN[unfolded N_def] by auto

  have m3c: "m3 \<in> carrier_mat n n" unfolding m3_def using h1a1_h2f2_h3 f1m1_f2 by auto
  {
    assume m3N: "m3 \<in> N" 
    note [simp] = h1a1 h2f2_h3 f h h2a1_h3 f1h1 m5
    note [simp] = mult_add_distrib_mat[of _ n n _ n]
    note [simp] = add_mult_distrib_mat[of _ n n _ _ n]
    note [simp] = mult_minus_distrib_mat[of _ n n _ n]
    note [simp] = assoc_mult_mat[of _ n n _ n _ n]
    note [simp] = uminus_add_minus_mat[of _ n n]
    note [simp] = mat_add_compo_alt mat_minus_compo_alt
    have [simp]: "a \<in> carrier_mat n n \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> (-a) $$ (i,j) = - (a $$ (i,j))" 
      for a :: "'a mat" and i j by simp
    have [simp]: "a \<in> carrier_mat n n \<Longrightarrow> b \<in> carrier_mat n n \<Longrightarrow> a * - b = - (a * b)" 
      for a b :: "'a mat" by simp
    have [simp]: "dim_row f2 = n" "dim_col f2 = n" using f by blast+
    have [simp]: "dim_row m5 = n" "dim_col m5 = n" using m5 by blast+

    let ?I = oneE\<^sub>I
    define m6 where "m6 = ?I * (f1h1 * h1a1 - h1a1) + ?I * (f1 * h2f2_h3 - h2f2_h3) + ?I * m5" 

    have I: "?I \<in> E\<^sub>I I" "?I \<in> carrier_mat n n" by (rule oneE\<^sub>I_E\<^sub>I, auto)
    hence "?I \<in> N" unfolding E\<^sub>I_def by auto
    from N_mult_closed[OF this m3N]  
    have "?I * m3 \<in> N" by auto
    also have "m3 = h1a1 + h2f2_h3 + - (f1h1 * h1a1 + f1h1 * h2a1_h3 + f1 * h2f2_h3 + f2)" 
      unfolding m3_def h1a1_h2f2_h3_def f1m1_f2_def f1m1_def m1_def f1h1_def
        h1_h1a1_h2a1_h3_def h1a1_h2a1_h3_def
      by (simp add: algebra_simps)
    also have "\<dots> = (h1a1 - f1h1 * h1a1) + (h2f2_h3 - f1 * h2f2_h3) - m5" 
      unfolding m5_def
      by (intro eq_matI, auto simp add: ac_simps)
    also have "\<dots> = - ((f1h1 * h1a1 - h1a1) + (f1 * h2f2_h3 - h2f2_h3) + m5)" 
      by (intro eq_matI, auto simp add: ac_simps)
    also have "?I * \<dots> = - m6" unfolding m6_def by simp
    finally have m6N: "- m6 \<in> N" by auto

    {
      fix a b
      assume E: "a \<in> E\<^sub>I I" "b \<in> E\<^sub>I I" 
      hence ab[simp]: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" "{a,b} \<subseteq> N" 
        using E\<^sub>IN unfolding N_def by auto
      from oneE\<^sub>I[OF E(1)] obtain c where cN: "c \<in> N" and a: "a = c + ?I" by auto
      hence c[simp]: "c \<in> carrier_mat n n" unfolding N_def by auto  
      have "?I * (a * b - b) = ?I * a * b - ?I * b" by simp
      also have "?I * a * b = ?I * c * b + ?I * b" unfolding a 
        by (simp add: oneE\<^sub>I_mult_oneE\<^sub>I)
      also have "\<dots> - ?I * b = ?I * c * b" by auto
      also have "\<dots> \<in> N" using E\<^sub>IN E oneE\<^sub>I_E\<^sub>I by (intro N_mult_closed cN, auto)
      finally have "?I * (a * b - b) \<in> N" .
    } note expr_in_N = this

    have "m6 \<in> E\<^sub>I I" unfolding m6_def using fE
      by (intro N_EI_add EI_EI_mult oneE\<^sub>I_E\<^sub>I m5E N_add_closed expr_in_N f1h1E h1a1E h2f2_h3E, auto)
    with i have "m6 $$ (i,i) \<ge> 1" unfolding E\<^sub>I_def by auto
    moreover from m6N i have "m6 $$ (i,i) \<le> 0" unfolding N_def mat_ge_def by auto
    ultimately have False using \<open>\<not> 1 \<le> 0\<close> by auto
  } note m3_not_N = this
  with m3c have m3: "m3 \<in> carrier_mat n n" "m3 \<noteq> 0\<^sub>m n n" unfolding N_def by auto
  have [simp]: "x \<in> carrier_mat n n \<Longrightarrow> - 1\<^sub>m n * x = - x" for x :: "'a mat" 
    by simp
  have [simp]: "x \<in> carrier_mat n n \<Longrightarrow> (- x = 0\<^sub>m n n) = (x = 0\<^sub>m n n)" for x :: "'a mat" 
    by (metis zero_minus uminus_eq_mat)
  have alp_poly: "alpha_lhs_minus_rhs rule = LPoly mc ((Y,m3) # rem)" 
    unfolding alpha_lhs_minus_rhs.simps lhs rhs rule_def
    unfolding sub_lpoly_def mc_def
    by (simp add: ring_mat_simps 
        h2f1 h1a1_h2f2_h3 f1m1_f2 f1h2f1 m3_def[symmetric])
      (simp add: Let_def ring_mat_simps XY m3 rem_def m4_def)
  have "0 < n" using I by auto
  hence [simp]: "1\<^sub>m n \<noteq> (0\<^sub>m n n :: 'a mat)" 
    by (auto simp: mat_eq_iff)
  from decide_lpoly_over_E_in_EPN[OF wf_alpha alp_poly, of N] inN
  have "m3 \<in> N" by auto
  with m3_not_N show False 
    by auto
qed

(* we show that the rule 
   f(Y,X) \<rightarrow> f(Y,f(a,X))
   cannot be oriented weakly by an E-I interpretation, if we demand that 
   the constant parts must be non-negative
   (and we have another proof where we show that this rule can be weakly oriented for
    an E-I interpretation without this restriction) 
*)
theorem core_matrix_interpretation_for_TRSs_with_nonnegative_constant_cannot_solve_example_rule: 
  fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> E\<^sub>I I \<and> length cs = k \<and> c \<in> carrier_mat n n" 
    "\<forall>as f. set as \<subseteq> E\<^sub>I I \<longrightarrow> \<alpha> f as \<in> E\<^sub>I I" 
    "\<forall> rule x. rule \<in> R2 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N"
    "\<forall> rule x. rule \<in> R1 \<longrightarrow> range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> P\<^sub>I I"
    and nonneg_const: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> c \<in> N" 
    and XY[simp]: "X \<noteq> Y" 
    and rule: "(Fun f [Var Y, Var X],  
    Fun f [Var Y, Fun f [Fun a [], Var X]]) 
    \<in> R1 \<union> R2" (is "(?lhs,?rhs) \<in> _")
  shows False
proof -
  from assms(1) have alph: "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
    unfolding E\<^sub>I_def by blast
  from I obtain i where i: "i < n" "i \<in> I" by auto
  have "\<not> 1 \<le> (0 :: 'a)"
    by (simp add: linorder_not_le)
  hence zE: "0\<^sub>m n n \<notin> E\<^sub>I I" unfolding E\<^sub>I_def using i by (auto intro!: bexI[of _ i])  

  have EI_EI_add: "x \<in> E\<^sub>I I \<Longrightarrow> y \<in> E\<^sub>I I \<Longrightarrow> x + y \<in> E\<^sub>I I" for x y 
    using N_EI_add[of x y] using E\<^sub>IN by auto

  note Al = assms(1)[rule_format]
  obtain fs f0 where Af: "Alpha (f, Suc (Suc 0)) = (fs,f0)" by force
  note Alf = Al[OF Af] 
  then obtain f1 f2 where fs: "fs = [f1,f2]" by (cases fs; cases "tl fs"; auto)
  note Af = Af[unfolded fs]
  from Alf[unfolded fs] E\<^sub>IN[unfolded N_def]
  have f: "f0 \<in> carrier_mat n n"
    "f1 \<in> carrier_mat n n"
    "f2 \<in> carrier_mat n n"
    and fE: "{f1,f2} \<subseteq> E\<^sub>I I" by auto
  hence fz: "f1 \<noteq> 0\<^sub>m n n" "f2 \<noteq> 0\<^sub>m n n" using zE by auto
  from nonneg_const[rule_format, OF Af] 
  have f0N: "f0 \<in> N" by auto

  obtain as a0 where Aa: "Alpha (a, 0) = (as,a0)" by force
  note Ala = Al[OF Aa] 
  hence as: "as = []" by (cases as, auto)
  note Aa = Aa[unfolded as]
  note [simp] = right_mult_zero_mat[of _ n n] 
  note [simp] = right_mult_one_mat[of _ n n]
  from Ala[unfolded as] E\<^sub>IN[unfolded N_def]
  have a: "a0 \<in> carrier_mat n n" by auto
  from assms(2)[rule_format, of Nil a]
  have aE: "a0 \<in> E\<^sub>I I" using Aa a by (auto simp: alpha_def)

  note mult[simp] = mult_carrier_mat[of _ n n _ n] 
  note [simp] = minus_carrier_mat[of _ n n]
  note add[simp] = add_carrier_mat[of _ n n]
  note [simp] = uminus_carrier_mat[of _ n n]

  define f2f2 where "f2f2 = f2 * f2" 
  have f2f2E: "f2f2 \<in> E\<^sub>I I" using fE unfolding f2f2_def using EI_EI_mult by auto
  with E\<^sub>IN[unfolded N_def] zE have f2f2: "f2f2 \<in> carrier_mat n n" "f2f2 \<noteq> 0\<^sub>m n n" by auto

  have YX[simp]: "Y \<noteq> X" using XY by metis

  have lhs: "poly_of ?lhs = LPoly f0 [(X, f2), (Y, f1)]"
    by (simp add: alphap_def Af Aa ring_mat_simps var_lpoly_def a f fz)

  have rhs: "poly_of ?rhs = LPoly (f2 * (f1 * a0 + f0) + f0) [(X, f2f2), (Y, f1)]"
    by (simp add: alphap_def Af Aa ring_mat_simps var_lpoly_def a f fz 
       f2f2_def[symmetric] f2f2)

  define rule where "rule = (?lhs,?rhs)" 
  from assms(3,4,7)[unfolded P\<^sub>I_def, folded rule_def] 
  have inN: "\<forall> x. range x \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N" 
    by blast
  from wf_alpha_lhs_minus_rhs[of rule] assms(1)
  have wf_alpha: "wf_lpoly mat_sq_ring (alpha_lhs_minus_rhs rule)" 
    unfolding E\<^sub>I_def N_def by force
  define \<gamma> :: "'v \<Rightarrow> 'a mat" where "\<gamma> x = oneE\<^sub>I" for x
  have ran: "range \<gamma> \<subseteq> E\<^sub>I I" unfolding \<gamma>_def using oneE\<^sub>I_E\<^sub>I by auto
  hence wf_ass: "wf_ass mat_sq_ring \<gamma>" unfolding wf_ass_def E\<^sub>I_def N_def
    by (auto simp: ring_mat_simps)

  let ?I = oneE\<^sub>I

  note [simp] = mult_add_distrib_mat[of _ n n _ n]
  note [simp] = add_mult_distrib_mat[of _ n n _ _ n]
  note [simp] = mult_minus_distrib_mat[of _ n n _ n]
  note [simp] = assoc_mult_mat[of _ n n _ n _ n]
  note [simp] = uminus_add_minus_mat[of _ n n]
  note [simp] = mat_add_compo_alt mat_minus_compo_alt
  
  have [simp]: "dim_row f1 = n" using f by auto
  have [simp]: "dim_row f2 = n" using f by auto
  have [simp]: "dim_row f2f2 = n" using f2f2 by auto
  have [simp]: "dim_col oneE\<^sub>I = n" using oneE\<^sub>I_carrier by blast

  define m1 where "m1 = f0 + f1 * ?I" 
  have m1[simp]: "m1 \<in> carrier_mat n n" unfolding m1_def by auto
  define m2 where "m2 = f2 * (f1 * a0 + f0)" 
  have m2[simp]: "m2 \<in> carrier_mat n n" unfolding m2_def using f a by simp
  define m3 where "m3 = f2f2 * oneE\<^sub>I - f2 * oneE\<^sub>I" 
  have m3[simp]: "m3 \<in> carrier_mat n n" unfolding m3_def using f a by simp
  define m4 where "m4 = ?I * (m2 + m3)" 
  have m4[simp]: "m4 \<in> carrier_mat n n" unfolding m4_def by simp

  from inN[rule_format, OF ran, unfolded rule_def alpha_lhs_minus_rhs.simps]
  have "eval_lpoly mat_sq_ring \<gamma> (poly_of ?lhs) - eval_lpoly mat_sq_ring \<gamma> (poly_of ?rhs)
    \<in> N"  
    unfolding eval_sub_lpoly[OF wf_poly_of[OF alph] wf_poly_of[OF alph] wf_ass] by auto
  also have "eval_lpoly mat_sq_ring \<gamma> (poly_of ?lhs) = f0 + (f2 * ?I + f1 * ?I)"
    unfolding lhs \<gamma>_def by (simp add: ring_mat_simps f)
  also have "\<dots> = m1 + f2 * ?I" unfolding m1_def
    by (metis mult assoc_add_mat comm_add_mat f(1,2,3) oneE\<^sub>I_carrier)
  also have "eval_lpoly mat_sq_ring \<gamma> (poly_of ?rhs) = m2 + f0 + (f2f2 * ?I + f1 * ?I)"
    unfolding rhs \<gamma>_def by (simp add: ring_mat_simps f m2_def)
  also have "\<dots> = m1 + (m2 + f2f2 * ?I)" unfolding m1_def using f 
    by (smt (verit, ccfv_SIG) m1 m2 add_carrier_mat
        assoc_add_mat comm_add_mat f2f2(1) m1_def mult_carrier_mat oneE\<^sub>I_carrier)
  also have "m1 + f2 * ?I - \<dots> = f2 * ?I - (m2 + f2f2 * ?I)" 
    using f m1 m2 
    by (smt (verit, ccfv_threshold) add_carrier_mat comm_add_mat f2f2(1) minus_add_minus_mat
        mult_carrier_mat oneE\<^sub>I_carrier squared_ring_mat.mat_add_eq_minus)
  also have "\<dots> = - (m2 + m3)" unfolding m3_def 
    by (intro eq_matI, auto)
  finally have "- (m2 + m3) \<in> N" by auto
  with oneE\<^sub>I_E\<^sub>I have "?I * (- (m2 + m3)) \<in> N" 
    using E\<^sub>IN N_mult_closed by blast
  also have "?I * (- (m2 + m3)) = - m4" unfolding m4_def 
    by (metis carrier_matD(1,2) core_mat_inter.oneE\<^sub>I_carrier index_add_mat(2) m3
        uminus_mult_right_mat)
  finally have neg_m4: "- m4 \<in> N" by auto

  have "m2 = f2 * f0 + f2 * f1 * a0" unfolding m2_def using f a
    by (intro eq_matI, auto)
  also have "\<dots> \<in> E\<^sub>I I" using fE 
    by (intro N_EI_add N_mult_closed f0N EI_EI_mult aE, auto simp: E\<^sub>I_def)
  finally have m2: "?I * m2 \<in> E\<^sub>I I" using EI_EI_mult by (simp add: oneE\<^sub>I_E\<^sub>I)

  from fE have "f2 \<in> E\<^sub>I I" by auto
  from oneE\<^sub>I[OF this] obtain m5 where f2: "f2 = m5 + ?I" and m5N: "m5 \<in> N" by auto
  hence f2f2d: "f2f2 = (m5 + ?I) * f2" and m5[simp]: "m5 \<in> carrier_mat n n" 
    unfolding f2f2_def N_def by auto
  have "?I * m3 = ?I * m5 * f2 * ?I + (?I * ?I) * f2 * ?I - ?I * f2 * ?I" 
    unfolding m3_def f2f2d using f by (simp add: algebra_simps)
  also have "\<dots> = ?I * m5 * f2 * ?I" unfolding oneE\<^sub>I_mult_oneE\<^sub>I
    by fastforce
  also have "\<dots> \<in> N"  using fE oneE\<^sub>I_E\<^sub>I E\<^sub>IN by (intro N_mult_closed m5N, auto)
  finally have m3: "?I * m3 \<in> N" .

  from m2 m3 have "?I * m2 + ?I * m3 \<in> E\<^sub>I I" by (rule E\<^sub>I_N_closed)
  also have "?I * m2 + ?I * m3 = m4" unfolding m4_def by simp
  finally have m4E: "m4 \<in> E\<^sub>I I" by auto

  from E\<^sub>I_N_closed[OF m4E neg_m4] 
  have "0\<^sub>m n n \<in> E\<^sub>I I" using m4
    by (metis N_el_in_carr neg_m4 uminus_l_inv_mat uminus_uminus_mat)
  thus False using zE by blast
qed


theorem core_matrix_interpretation_for_TRSs_EI_sufficient: fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> E\<^sub>I I \<and> length cs = k \<and> c \<in> N \<and> (k = 0 \<longrightarrow> c \<in> E\<^sub>I I)" 
    "\<forall> rule c xcs. rule \<in> R1 \<union> R2 \<longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs \<longrightarrow> insert c (snd ` set xcs) \<subseteq> N"
    "\<forall> rule c xcs. rule \<in> R1 \<longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs \<longrightarrow> insert c (snd ` set xcs) \<inter> P\<^sub>I I \<noteq> {}"
  shows "SN (relto (rstep R1) (rstep R2))" 
  apply (rule core_matrix_interpretation_for_TRSs_sufficient[OF _ delta_pos E\<^sub>IN P\<^sub>IP N_P\<^sub>I_closed EI_PI_mult PI_EI_mult EI_EI_mult N_EI_add])
  subgoal using assms(1) E\<^sub>IN N_carrier by blast
               apply (insert assms, auto)[12]
  subgoal using assms(2) by blast
  subgoal using assms(3) by blast
  done
end

(* M\<^sub>I instance *)

lemma M\<^sub>IN: "M\<^sub>I I \<subseteq> N" unfolding M\<^sub>I_def by auto

lemma L\<^sub>IP: "L\<^sub>I I \<subseteq> P" unfolding L\<^sub>I_def P_def
proof (clarsimp simp: N_def mat_gt_def, goal_cases)
  case (1 a)
  from I obtain i where iI: "i \<in> I" by auto
  with 1 obtain j where jI: "j \<in> I" and delt: "\<delta> \<le> a $$ (i, j)" by auto
  from iI jI I have ij: "i < n" "j < n" by auto
  show ?case 
    apply (rule exI[of _ i])
    apply (rule conjI[OF ij(1) exI[of _ j]])
    using 1 ij delt by auto
qed

lemma N_L\<^sub>I_closed: assumes "a \<in> N" "b \<in> L\<^sub>I I"
  shows "a + b \<in> L\<^sub>I I" 
proof -
  from assms[unfolded L\<^sub>I_def] 
  have delt: "\<And> i. i \<in> I \<Longrightarrow> \<exists> j \<in> I. b $$ (i,j) \<ge> \<delta>" 
     and b: "b \<in> N" by auto
  from assms b have abN: "a + b \<in> N" by (metis N_add_closed)
  {
    fix i 
    assume i: "i \<in> I" 
    with delt obtain j where j: "j \<in> I" and delt: "b $$ (i,j) \<ge> \<delta>" by auto
    from i j I have ij': "i < n" "j < n" by auto
    from assms(1) ij' have a: "a $$ (i,j) \<ge> 0" unfolding N_def mat_ge_def by auto
    have ab: "(a + b) $$ (i, j) = a $$ (i,j) + b $$ (i,j)" using assms b ij' unfolding N_def by auto
    also have "\<dots> \<ge> 0 + \<delta>" using delt a by (metis plus_mono)
    finally have "\<exists> j \<in> I. (a + b) $$ (i,j) \<ge> \<delta>" using j by auto
  }
  thus ?thesis using abN unfolding L\<^sub>I_def by auto
qed

context
  assumes delta_pos: "\<delta> > 0" 
begin

lemma MI_LI_mult: assumes "a \<in> M\<^sub>I I" "b \<in> L\<^sub>I I" 
  shows "a * b \<in> L\<^sub>I I" 
proof -
  from assms[unfolded L\<^sub>I_def M\<^sub>I_def] 
  have aN: "a \<in> N" and bN: "b \<in> N" by auto 
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding L\<^sub>I_def
  proof (clarify, intro conjI abN, intro ballI)
    fix i
    assume i: "i \<in> I" 
    from assms[unfolded M\<^sub>I_def] i obtain k where k: "k \<in> I" and a: "a $$ (i,k) \<ge> 1" by auto
    from assms[unfolded L\<^sub>I_def] k obtain j where j: "j \<in> I" and b: "b $$ (k,j) \<ge> \<delta>" by auto
    from i j k I have ij: "i < n" "j < n" and k: "k < n" by auto
    have "(a * b) $$ (i, j) = (\<Sum>l \<in> {..<n}. a $$ (i, l) * b $$ (l, j))" 
      by (subst mat_mult_compo_alt[OF ab ij], auto)
    also have "\<dots> = a $$ (i, k) * b $$ (k, j) + (\<Sum>l \<in> {..<n} - {k}. a $$ (i, l) * b $$ (l, j))" 
      by (subst sum.remove[of _ k], insert ij k, auto)
    also have "\<dots> \<ge> 1 * \<delta> + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg a delta0[OF delta_pos] b)
      by (insert aN bN ij k, auto simp: N_def)
    finally show "\<exists> j \<in> I. \<delta> \<le> (a * b) $$ (i, j) - 0" using j by auto
  qed
qed

lemma LI_MI_mult: assumes "a \<in> L\<^sub>I I" "b \<in> M\<^sub>I I" 
  shows "a * b \<in> L\<^sub>I I" 
proof -
  from assms[unfolded L\<^sub>I_def M\<^sub>I_def] 
  have aN: "a \<in> N" and bN: "b \<in> N" by auto 
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding L\<^sub>I_def
  proof (clarify, intro conjI abN, intro ballI)
    fix i
    assume i: "i \<in> I" 
    from assms[unfolded L\<^sub>I_def] i obtain k where k: "k \<in> I" and a: "a $$ (i,k) \<ge> \<delta>" by auto
    from assms[unfolded M\<^sub>I_def] k obtain j where j: "j \<in> I" and b: "b $$ (k,j) \<ge> 1" by auto
    from i j k I have ij: "i < n" "j < n" and k: "k < n" by auto
    have "(a * b) $$ (i, j) = (\<Sum>l \<in> {..<n}. a $$ (i, l) * b $$ (l, j))" 
      by (subst mat_mult_compo_alt[OF ab ij], auto)
    also have "\<dots> = a $$ (i, k) * b $$ (k, j) + (\<Sum>l \<in> {..<n} - {k}. a $$ (i, l) * b $$ (l, j))" 
      by (subst sum.remove[of _ k], insert ij k, auto)
    also have "\<dots> \<ge> \<delta> * 1 + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg a delta0 b)
      by (insert aN bN ij k, auto simp: N_def)
    finally show "\<exists> j \<in> I. \<delta> \<le> (a * b) $$ (i, j) - 0" using j by auto
  qed
qed

lemma MI_MI_mult: assumes "a \<in> M\<^sub>I I" "b \<in> M\<^sub>I I" 
  shows "a * b \<in> M\<^sub>I I" 
proof -
  from assms[unfolded L\<^sub>I_def M\<^sub>I_def] 
  have aN: "a \<in> N" and bN: "b \<in> N" by auto 
  from aN bN have abN: "a * b \<in> N" by (rule N_mult_closed)
  from aN bN have ab: "a \<in> carrier_mat n n" "b \<in> carrier_mat n n" unfolding N_def by auto
  show ?thesis unfolding M\<^sub>I_def
  proof (clarify, intro conjI abN, intro ballI)
    fix i
    assume i: "i \<in> I" 
    from assms[unfolded M\<^sub>I_def] i obtain k where k: "k \<in> I" and a: "a $$ (i,k) \<ge> 1" by auto
    from assms[unfolded M\<^sub>I_def] k obtain j where j: "j \<in> I" and b: "b $$ (k,j) \<ge> 1" by auto
    from i j k I have ij: "i < n" "j < n" and k: "k < n" by auto
    have "(a * b) $$ (i, j) = (\<Sum>l \<in> {..<n}. a $$ (i, l) * b $$ (l, j))" 
      by (subst mat_mult_compo_alt[OF ab ij], auto)
    also have "\<dots> = a $$ (i, k) * b $$ (k, j) + (\<Sum>l \<in> {..<n} - {k}. a $$ (i, l) * b $$ (l, j))" 
      by (subst sum.remove[of _ k], insert ij k, auto)
    also have "\<dots> \<ge> 1 * 1 + 0" 
      apply (intro add_mono mult_mono sum_nonneg mult_nonneg_nonneg a delta0 b)
      by (insert aN bN ij k, auto simp: N_def)
    finally show "\<exists> j \<in> I. 1 \<le> (a * b) $$ (i, j)" using j by auto
  qed
qed

lemma N_MI_add: assumes "a \<in> N" "b \<in> M\<^sub>I I" 
  shows "a + b \<in> M\<^sub>I I"
  using assms unfolding M\<^sub>I_def using N_add_closed[of a b] N_el_in_carr[of a] N_el_in_carr[of b]
proof (clarsimp, clarify, goal_cases)
  case (1 i)
  then obtain j where j: "j \<in> I" and b: "1 \<le> b $$ (i, j)" by auto
  from 1 j I have ij: "i < n" "j < n" by auto
  from assms ij have a: "a $$ (i,j) \<ge> 0" unfolding N_def by auto 
  from ij a b j show ?case by (intro bexI[of _ j], insert 1, auto simp: add_increasing)
qed

theorem core_matrix_interpretation_for_TRSs_MI: fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> M\<^sub>I I \<and> length cs = k \<and> c \<in> carrier_mat n n" 
    "\<forall>as f. set as \<subseteq> M\<^sub>I I \<longrightarrow> \<alpha> f as \<in> M\<^sub>I I" 
    "\<forall> rule x. rule \<in> R2 \<longrightarrow> range x \<subseteq> M\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> N"
    "\<forall> rule x. rule \<in> R1 \<longrightarrow> range x \<subseteq> M\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring x (alpha_lhs_minus_rhs rule) \<in> L\<^sub>I I"
  shows "SN (relto (rstep R1) (rstep R2))"  
  by (rule core_matrix_interpretation_for_TRSs[OF _ delta_pos M\<^sub>IN L\<^sub>IP N_L\<^sub>I_closed MI_LI_mult],
    insert assms, fastforce intro!: set_mp[OF M\<^sub>IN], auto)

lemma M\<^sub>I_carrier: "M\<^sub>I I \<subseteq> carrier_mat n n" 
  unfolding M\<^sub>I_def N_def by auto

theorem core_matrix_interpretation_for_TRSs_MI_sufficient: fixes R1 R2 :: "('f,'v)trs" 
  assumes "\<forall>f k cs c. Alpha (f, k) = (cs, c) \<longrightarrow> set cs \<subseteq> M\<^sub>I I \<and> length cs = k \<and> c \<in> N \<and> (k = 0 \<longrightarrow> c \<in> M\<^sub>I I)" 
    "\<forall> rule c xcs. rule \<in> R1 \<union> R2 \<longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs \<longrightarrow> insert c (snd ` set xcs) \<subseteq> N"
    "\<forall> rule c xcs. rule \<in> R1 \<longrightarrow> alpha_lhs_minus_rhs rule = LPoly c xcs \<longrightarrow> insert c (snd ` set xcs) \<inter> L\<^sub>I I \<noteq> {}"
  shows "SN (relto (rstep R1) (rstep R2))" 
  apply (rule core_matrix_interpretation_for_TRSs_sufficient[OF _ delta_pos M\<^sub>IN L\<^sub>IP N_L\<^sub>I_closed MI_LI_mult LI_MI_mult MI_MI_mult N_MI_add])
  subgoal using assms(1) M\<^sub>IN N_carrier by blast
               apply (insert assms, auto)[12]
  subgoal using assms(2) by blast
  subgoal using assms(3) by blast
  done
end


lemma check_lpoly_generic_EI: assumes wf: "wf_lpoly mat_sq_ring p"
  and cond: "\<forall> a. a \<in> carrier_mat n n \<longrightarrow> cond a \<longrightarrow> a \<in> EPN"
  and EPN: "EPN \<in> {E\<^sub>I I, P\<^sub>I I, N}" 
  and check: "check_lpoly_generic_EI cond p" 
shows "\<forall> \<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> EPN"
proof (cases p)
  case (LPoly c xcs)
  show ?thesis
  proof (subst decide_lpoly_over_E_in_EPN[OF wf LPoly EPN])
    from check[unfolded LPoly, simplified]
    have c1: "cond (eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) (LPoly c xcs))" and xcs1: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<ge>\<^sub>m 0\<^sub>m n n" by auto
    from wf[unfolded LPoly, simplified, unfolded wf_pvars_def]
    have xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
      by (auto simp: ring_mat_def)
    have c2: "eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p \<in> carrier_mat n n" using wf mring.wf_eval_lpoly[of _ p] 
      by (auto simp: ring_mat_simps wf_ass_def)
    from c1 c2 cond LPoly have c: "eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p \<in> EPN" by auto
    have xcs: "snd xci \<in> N" if "xci \<in> set xcs" for xci using xcs1[OF that] xcs2[OF that]
      unfolding N_def by simp
    show "snd ` set xcs \<subseteq> N \<and> eval_lpoly mat_sq_ring (\<lambda>_. oneE\<^sub>I) p \<in> EPN" using xcs c by auto
  qed
qed

lemma check_lpoly_EI_N: assumes wf: "wf_lpoly mat_sq_ring p" 
  and check: "check_lpoly_EI_N p" 
shows "\<forall> \<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> N"
  by (rule check_lpoly_generic_EI[OF wf _ _ check[unfolded check_lpoly_EI_N_def]])
    (auto simp: N_def)

lemma check_lpoly_EI_EI: assumes wf: "wf_lpoly mat_sq_ring p" 
  and check: "check_lpoly_EI_EI p" 
shows "\<forall> \<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> E\<^sub>I I"
  apply (rule check_lpoly_generic_EI[OF wf _ _ check[unfolded check_lpoly_EI_EI_def]])
  using in_E\<^sub>I_criterion by auto

lemma check_lpoly_EI_PI: assumes wf: "wf_lpoly mat_sq_ring p" 
  and Il: "set Il = I" 
  and check: "check_lpoly_EI_PI Il p" 
shows "\<forall> \<gamma>. range \<gamma> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<gamma> p \<in> P\<^sub>I I"
  apply (rule check_lpoly_generic_EI[OF wf _ _ check[unfolded check_lpoly_EI_PI_def]])
   apply (unfold Il)
  by (auto simp: P\<^sub>I_def N_def)


lemma EI_conds: "E\<^sub>I I \<noteq> {}" "E\<^sub>I I \<subseteq> carrier_mat n n" using one_in_EI 
  unfolding E\<^sub>I_def N_def by auto


context (* syntactic shape of Alpha is correct + restriction to N for coefficients *)
  assumes Alphapre: "\<forall> f k cs c. Alpha (f,k) = (cs,c) \<longrightarrow> set cs \<subseteq> N \<and> length cs = k \<and> c \<in> carrier_mat n n" 
  and delta0: "\<delta> \<ge> 0" 
begin

private lemmas preconds = Alphapre EI_conds

lemma inter_lpoly_EI: assumes
  "\<forall> \<beta>. range \<beta> \<subseteq> E\<^sub>I I \<longrightarrow> eval_lpoly mat_sq_ring \<beta> (inter_lpoly (f,k)) \<in> E\<^sub>I I" 
  and "length as = k" and "set as \<subseteq> E\<^sub>I I" 
shows "\<alpha> f as \<in> E\<^sub>I I"
  by (rule inter_lpoly[OF preconds assms])

lemma valid_interpretation_criterion: assumes
  "check_lpoly_EI_EI (inter_lpoly (f, k))" 
  and "length as = k" and "set as \<subseteq> E\<^sub>I I" 
shows "\<alpha> f as \<in> E\<^sub>I I"
  apply (rule inter_lpoly[OF preconds _ assms(2-3)])
  apply (rule check_lpoly_EI_EI)
  apply (rule wf_inter_lpoly[OF Alphapre])
  using assms(1) .

lemma Alpha_list_to_Alpha_EI: assumes "Alpha = Alpha_list_to_Alpha def fk_cs" 
  and def: "def = (\<delta> + 1) \<cdot>\<^sub>m 1\<^sub>m n" 
  and fk_cs: "\<And> f c. (f,c) \<in> set fk_cs \<Longrightarrow> check_lpoly_EI_EI (inter_lpoly f)"
shows "\<forall> as f. set as \<subseteq> E\<^sub>I I \<longrightarrow> \<alpha> f as \<in> E\<^sub>I I" 
proof (intro allI impI)
  fix as f
  assume as: "set as \<subseteq> E\<^sub>I I" 
  let ?k = "length as" 
  show "\<alpha> f as \<in> E\<^sub>I I" 
  proof (cases "map_of fk_cs (f,?k)")
    case (Some pair)
    then obtain cs c where map: "map_of fk_cs (f,?k) = Some (cs,c)" by force  
    hence Alpha: "Alpha (f,?k) = (cs,c)" unfolding assms Alpha_list_to_Alpha_def by auto
    from fk_cs[OF map_of_SomeD[OF map]] 
    have "check_lpoly_EI_EI (inter_lpoly (f, ?k))" by auto
    from valid_interpretation_criterion[OF this _ as]
    show ?thesis by auto
  next
    case None
    hence Alpha: "Alpha (f,?k) = default_Alpha def (f,?k)" unfolding assms Alpha_list_to_Alpha_def by auto  
    define sum where "sum = sum_list_mat (map2 (*) (replicate (length as) (1\<^sub>m n)) as)" 
    {
      fix i
      assume "i < length as" 
      hence "as ! i \<in> E\<^sub>I I" using as by auto
      hence "as ! i \<in> N" unfolding E\<^sub>I_def by auto
      hence "1\<^sub>m n * as ! i \<in> N" unfolding N_def by auto
    } note asN = this
    hence sumN: "sum \<in> N" unfolding sum_def
      by (intro sum_list_mat_N, auto simp: set_conv_nth)
    have EI: "def \<in> E\<^sub>I I" unfolding E\<^sub>I_def N_def def using delta0 I
      by auto
    have "\<alpha> f as = sum + def" 
      unfolding alpha_def Alpha split default_Alpha_def Let_def snd_conv sum_def by auto
    also have "\<dots> \<in> E\<^sub>I I" using sumN EI
      by (metis E\<^sub>I_N_closed N_el_in_carr add_carrier_mat comm_add_mat oneE\<^sub>I oneE\<^sub>I_carrier)
    finally show ?thesis .
  qed
qed

lemma eval_lpoly_member_via_MI: assumes wf: "wf_lpoly mat_sq_ring p"
  and E: "E = (if b then M\<^sub>I I else L\<^sub>I I)" 
  and diff: "diff = (if b then 1 else \<delta>)" 
  and p: "p = LPoly c xcs" 
  and xcs: "insert c (snd ` set xcs) \<subseteq> N" 
  and inE: "\<forall> i \<in> I. \<exists> d \<in> insert c (snd ` set xcs). \<exists> j \<in> I. d $$ (i,j) \<ge> diff" 
  and gam: "range \<gamma> \<subseteq> M\<^sub>I I"
shows "eval_lpoly mat_sq_ring \<gamma> p \<in> E"
proof -
  from wf[unfolded p, simplified, unfolded wf_pvars_def]
  have c2: "c \<in> carrier_mat n n" and xcs2: "\<And> xci. xci \<in>set xcs \<Longrightarrow> snd xci \<in> carrier_mat n n" 
    by (auto simp: ring_mat_def)
  define d where "d = eval_pvars mat_sq_ring \<gamma> xcs" 
  have Mn: "a \<in> M\<^sub>I I \<Longrightarrow> a \<in> carrier_mat n n" for a unfolding M\<^sub>I_def N_def by auto
  define prods where "prods = map (\<lambda> (x,c). c * \<gamma> x) xcs"
  have prods: "set prods \<subseteq> carrier_mat n n" using xcs2 gam Mn
    by (fastforce simp: prods_def intro!: mult_carrier_mat[of _ n n])  
  from xcs have xcsn: "snd ` set xcs \<subseteq> carrier_mat n n" unfolding N_def by auto
  have "sum_list_mat prods = eval_pvars mat_sq_ring \<gamma> xcs" unfolding prods_def
  proof (induct xcs)
    case Nil
    show ?case by (auto simp: ring_mat_simps)
  next
    case (Cons xc xcs)
    obtain x c where xc: "xc = (x,c)" by force
    thus ?case using Cons by (auto simp: ring_mat_simps)
  qed
  hence id: "eval_lpoly mat_sq_ring \<gamma> p = c + sum_list_mat prods" 
    unfolding d_def p by (simp add: ring_mat_simps)
  have gamN: "\<gamma> x \<in> N" for x using gam M\<^sub>IN by auto
  have prodsN: "set prods \<subseteq> N" unfolding prods_def using xcs gamN
    by (auto intro!: N_mult_closed)
  hence sumN: "sum_list_mat prods \<in> N" by auto
  have inN: "eval_lpoly mat_sq_ring \<gamma> p \<in> N" unfolding id using xcs sumN
    using N_add_closed by auto
  {
    fix i
    assume i: "i \<in> I" 
    from inE[rule_format, OF this] obtain d j
      where d: "d \<in> insert c (snd ` set xcs)" and j: "j \<in> I" and diff: "d $$ (i,j) \<ge> diff" by auto    
    from i j have ij: "i < n" "j < n" using I by auto
    have "\<exists> j \<in> I. eval_lpoly mat_sq_ring \<gamma> p $$ (i,j) \<ge> diff"
    proof (cases "d = c")
      case True
      from sumN ij have "sum_list_mat prods $$ (i,j) \<ge> 0" by (metis N_compo_greater_eq_zero)
      hence "eval_lpoly mat_sq_ring \<gamma> p $$ (i,j) \<ge> diff" unfolding id using diff[unfolded True]
        sumN ij unfolding N_def by (auto simp: add_increasing2)
      with j show ?thesis by auto
    next
      case False
      then obtain x where "(x,d) \<in> set xcs" using d by auto
      then obtain k where k: "k < length xcs" and xcsk: "xcs ! k = (x,d)" by (auto simp: set_conv_nth)
      define prodk where "prodk = take k prods @ drop (Suc k) prods" 
      have sub: "set prodk \<subseteq> set prods" unfolding prodk_def by (auto elim: in_set_takeD in_set_dropD)
      have prodkN: "sum_list_mat prodk \<in> N" using prodsN sub by auto
      from d xcs have dN: "d \<in> N" and cN: "c \<in> N" by auto
      from gamN[of x] have \<gamma>N: "\<gamma> x \<in> N" by auto
      from dN \<gamma>N cN prodkN 
      have carr: "d \<in> carrier_mat n n" "c \<in> carrier_mat n n" "sum_list_mat prodk \<in> carrier_mat n n" "\<gamma> x \<in> carrier_mat n n" 
        by (auto simp: N_def)
      define e where "e = c + sum_list_mat prodk" 
      have eN: "e \<in> N" unfolding e_def using cN prodkN by (rule N_add_closed)
      hence e: "e \<in> carrier_mat n n" unfolding N_def by auto

      from k have "k < length prods" by (auto simp: prods_def)
      from sum_list_split[OF prods this]
      have "sum_list_mat prods = prods ! k + sum_list_mat prodk" unfolding prodk_def
        by auto
      also have "prods ! k = d * \<gamma> x" unfolding prods_def using xcsk k by auto
      finally have "eval_lpoly mat_sq_ring \<gamma> p = c + (d * \<gamma> x + sum_list_mat prodk)" unfolding id
        by simp
      also have "\<dots> = e + d * \<gamma> x" unfolding e_def using carr by auto
      finally have id: "eval_lpoly mat_sq_ring \<gamma> p = e + d * \<gamma> x" by auto

      from gam have "\<gamma> x \<in> M\<^sub>I I" by auto
      from this[unfolded M\<^sub>I_def] j obtain l where lI: "l \<in> I" and ge1: "\<gamma> x $$ (j,l) \<ge> 1" by auto
      from lI have l: "l < n" using I by auto
      have "(d * \<gamma> x) $$ (i,l) = (\<Sum>k<n. d $$ (i, k) * \<gamma> x $$ (k, l))" 
        by (rule mat_mult_compo_alt, insert carr ij l, auto)
      also have "\<dots> = d $$ (i, j) * \<gamma> x $$ (j, l) + (\<Sum>k\<in>{..<n} - {j}. d $$ (i, k) * \<gamma> x $$ (k, l))" 
        by (rule sum.remove[of _ j], insert ij, auto)
      also have "\<dots> \<ge> diff * 1 + 0" 
      proof (intro add_mono mult_mono diff ge1 sum_nonneg mult_nonneg_nonneg)
        show "0 \<le> d $$ (i, j)" using diff delta0 assms(3) 
          by (cases b, auto) 
      qed (insert dN \<gamma>N ij l, auto simp: N_def mat_ge_def)
      finally have "(d * \<gamma> x) $$ (i,l) \<ge> diff" by auto
      hence "eval_lpoly mat_sq_ring \<gamma> p $$ (i,l) \<ge> diff" 
        unfolding id using carr e ij l eN
        by (auto simp: N_def mat_ge_def add_increasing)
      with lI show ?thesis by auto
    qed
  }
  with inN show ?thesis using diff E 
    by (cases b, auto simp: M\<^sub>I_def L\<^sub>I_def)
qed

end (* basic demands on Alpha *)
end (* conditions on I *)
end (* fixing I *)
end (* fixing interpretation Alpha *)
end (* locale that fixes dimension n, parameter \<delta> and carrier (via type 'a) *)
 
lemmas core_mat_inter_code =
  core_mat_inter.alpha_lhs_minus_rhs.simps
  core_mat_inter.subst_lpoly.simps
  core_mat_inter.oneE\<^sub>I_def
  core_mat_inter.sub_lpoly_def
  core_mat_inter.alphap_def
  core_mat_inter.check_lpoly_EI_PI_def
  core_mat_inter.check_lpoly_EI_EI_def
  core_mat_inter.check_lpoly_EI_N_def
  core_mat_inter.check_lpoly_generic_EI.simps
  core_mat_inter.inter_lpoly_def
  core_mat_inter.Alpha_list_to_Alpha_def
  core_mat_inter.default_Alpha_def
  core_mat_inter.core_mat_af_def
  

declare core_mat_inter_code[code]

end (* theory *)

