theory Matrix_Base
  imports
    Jordan_Normal_Form.Matrix_Comparison
    "Abstract-Rewriting.SN_Order_Carrier"
begin

lemma list_split_length_exI_trivial:
  assumes "length xs = length (a\<^sub>1@a\<^sub>2)"
  shows "\<exists> xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1@xs\<^sub>2 \<and> length xs\<^sub>1 = length a\<^sub>1 \<and> length xs\<^sub>2 = length a\<^sub>2"
  by (rule exI[of _ "take (length a\<^sub>1) xs"], rule exI[of _ "drop (length a\<^sub>1) xs"],
    insert assms, auto)

lemma list_cons_length_exI_trivial:
  assumes "length xs = length (c#cs)"
  shows "\<exists>x xss. xs = x#xss \<and> length xss = length cs"
  using assms length_Suc_conv by auto


text \<open>Considering only matrices of integers and of dimension $n\times n$.\<close>

locale squared_ring_mat = 
  fixes n :: nat
    and gt :: "'a :: {ring_1,ordered_semiring_1,Rings.ordered_semiring_0} \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<succ>\<close> 50)
begin

abbreviation Mat_gt :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" (infix ">\<^sub>m" 50) where
   "Mat_gt \<equiv> mat_gt (\<succ>) n" 

definition interp_add_monoid_mat where
"interp_add_monoid_mat = monoid_mat TYPE('a) n n"

definition interp_mul_monoid_mat :: "'a mat monoid" where
"interp_mul_monoid_mat = \<lparr>carrier = carrier_mat n n, mult=(*), one=1\<^sub>m n\<rparr>"

definition interp_ring_mat where
"interp_ring_mat = ring_mat TYPE('a) n"


lemma add_monoid_mat_is_submonoid: "submonoid (carrier_mat n n) interp_add_monoid_mat"
  unfolding interp_add_monoid_mat_def monoid_mat_def
  using add_carrier_mat zero_carrier_mat by (simp add: submonoid_def)

lemma mul_monoid_mat_is_submonoid: "submonoid (carrier_mat n n) interp_mul_monoid_mat"
  unfolding interp_mul_monoid_mat_def
  using mult_carrier_mat one_carrier_mat by (simp add: submonoid_def)



interpretation inter_mat_monoid: monoid interp_mul_monoid_mat
  unfolding interp_mul_monoid_mat_def monoid_mat_def  
proof (unfold_locales, goal_cases)
  case (1 x y)
  then show ?case using mult_carrier_mat by simp
next
  case (2 x y z)
  then show ?case using assoc_mult_mat by simp
next
  case 3
  then show ?case using one_carrier_mat by simp
next
  case (4 x)
  then show ?case using left_mult_one_mat by simp
next
  case (5 x)
  then show ?case using right_mult_one_mat by simp
qed



text \<open>Zero matrix properties\<close>

lemma zero_minus: "(0\<^sub>m n n :: 'a mat) = -0\<^sub>m n n"
proof (standard, goal_cases)
  case (1 i j)
  then show ?case using index_zero_mat(1) by simp
qed auto


text \<open>Alternative definitions to matrix non-equality\<close>

lemma mat_neq_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A \<noteq> B = (\<exists>i j. i < n \<and> j < n \<and> A $$ (i,j) \<noteq> B $$ (i,j))"
  using assms by auto



text \<open>Alternative definitions to matrix multiplication and addition\<close>

lemma mat_mult_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
  shows "(A * B) $$ (i,j) = (\<Sum>k \<in> {..< n}. A $$ (i,k) * B $$ (k,j))"
  by (subst index_mult_mat, insert assms, auto simp: scalar_prod_def intro: sum.cong)

lemma mat_add_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
        shows "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
  using plus_mat_def index_mat assms carrier_matD by auto


lemma mat_minus_compo_alt:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
          "i < n" "j < n"
        shows "(A - B) $$ (i,j) = A $$ (i,j) - B $$ (i,j)"
  using minus_mat_def index_mat assms carrier_matD by auto



text \<open>Matrix equality equivalences\<close>


lemma mat_add_eq_minus: 
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B = C \<longleftrightarrow> A = C - B" 
proof 
  assume as: "A + B = C"
  show "A = C - B" unfolding as[symmetric] using assms
    by (intro eq_matI, auto)
next
  assume as: "A = C - B"
  show "A + B = C"
      unfolding as using assms by (intro eq_matI, auto)
qed



text \<open>Matrix comparison equivalences\<close>

lemma mat_cmp_minus_eq:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A \<ge>\<^sub>m B + C \<longleftrightarrow> (A - C \<ge>\<^sub>m B)"
proof -
  have "(A \<ge>\<^sub>m B + C) \<longleftrightarrow> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) \<ge> B $$ (i,j) + C $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_add_compo_alt by auto
  moreover
  have "(A - C \<ge>\<^sub>m B) \<longleftrightarrow> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) - C $$ (i,j) \<ge> B $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_minus_compo_alt by auto
  ultimately show ?thesis
    by (metis (mono_tags, lifting) add_diff_cancel_right' add_uminus_conv_diff plus_left_mono) 
qed

lemma mat_minus_cmp_eq:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B \<ge>\<^sub>m C \<longleftrightarrow> (A \<ge>\<^sub>m C - B)"
proof -
  have "(A + B \<ge>\<^sub>m C) \<longleftrightarrow> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) + B $$ (i,j) \<ge> C $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_add_compo_alt by auto
  moreover
  have "(A \<ge>\<^sub>m C - B) \<longleftrightarrow> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i,j) \<ge> C $$ (i,j) - B $$ (i,j))"
    using assms mat_ge_def carrier_matD mat_minus_compo_alt by auto
  ultimately show ?thesis 
    by (metis (mono_tags, lifting) add_diff_cancel_right' add_uminus_conv_diff plus_left_mono) 
qed

lemma mat_comparison_zero_eq:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A \<ge>\<^sub>m B \<longleftrightarrow> A - B \<ge>\<^sub>m 0\<^sub>m n n"
  using assms mat_cmp_minus_eq[of A "0\<^sub>m n n"] left_add_zero_mat by auto



lemma mat_comparison_eq_imp_nonneg_diff:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "A \<ge>\<^sub>m B"
  shows "\<exists>C. C \<ge>\<^sub>m 0\<^sub>m n n \<and> A = B + C"
proof
  have "A - B \<ge>\<^sub>m 0\<^sub>m n n" using mat_comparison_zero_eq[OF assms(1,2)] assms(3) by auto
  moreover
  have "B + (A - B) = A"
    using uminus_l_inv_mat[OF assms(2)] add_uminus_minus_mat[symmetric, OF assms(1,2)]
          assms(1,2) by auto
  ultimately show "A - B \<ge>\<^sub>m 0\<^sub>m n n \<and> A = B + (A - B)" by auto
qed

text \<open>Matrix multiplication associativity properties for more complex expressions\<close>

lemma mat_mult_assoc_4:
  assumes "A \<in> carrier_mat n n"
          "B \<in> carrier_mat n n"
          "C \<in> carrier_mat n n"
          "D \<in> carrier_mat n n"
  shows "(A * B) * (C * D) = A * (B * C) * D"
proof -
  have "(A * B) * (C * D) = A * (B * (C * D))"
    using assms mult_carrier_mat assoc_mult_mat[of A n n B n "C * D" n] by auto
  also have "\<dots> = A * ((B * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = (A * (B * C)) * D"
    using assms mult_carrier_mat assoc_mult_mat[of A n n "B * C" n] by auto
  finally show ?thesis.
qed

lemma mat_mult_assoc_5:
  assumes "A \<in> carrier_mat n n"
          "B \<in> carrier_mat n n"
          "C \<in> carrier_mat n n"
          "D \<in> carrier_mat n n"
          "E \<in> carrier_mat n n"
  shows "(A * B) * E * (C * D) = A * (B * E * C) * D"
proof -
  have "(A * B) * E * (C * D) = (A * B) * (E * (C * D))"
    using assms mult_carrier_mat assoc_mult_mat[of "A * B" n n E n "C * D" n] by auto
  also have "\<dots> = (A * B) * ((E * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = A * (B * ((E * C) * D))"
    using assms mult_carrier_mat assoc_mult_mat[of A n n B n "((E * C) * D)" n] by auto
  also have "\<dots> = A * ((B * (E * C)) * D)"
    using assms mult_carrier_mat assoc_mult_mat[of B n n "E * C" n] by auto
  also have "\<dots> = A * ((B * E * C) * D)"
    using assms mult_carrier_mat assoc_mult_mat by auto
  also have "\<dots> = A * (B * E * C) * D"
    using assms mult_carrier_mat assoc_mult_mat[of A n n "B * E * C" n] by auto
  finally show ?thesis.
qed
end

locale squared_ring_mat_with_assms = squared_ring_mat n gt 
  + SN_strict_mono_ordered_semiring_1 def gt 
  for n :: nat and def :: "'a :: {ring_1,ordered_semiring_1,Rings.ordered_semiring_0}" 
    and gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<succ>\<close> 50) +
  assumes one_gt_zero: "1 \<succ> 0" 
begin

lemma mat_cmp_minus:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A >\<^sub>m B + C \<longleftrightarrow> A - C >\<^sub>m B"
proof 
  assume as: "A >\<^sub>m B + C"
  then obtain i j where ij_p: "A $$ (i,j) \<succ> B $$ (i,j) + C $$ (i,j)" "i < n" "j < n"
    using mat_gt_def mat_add_compo_alt assms(2,3) by auto
  from as have "A \<ge>\<^sub>m B + C" by auto
  then have "A - C \<ge>\<^sub>m B"
    using mat_cmp_minus_eq assms by auto
  moreover
  from ij_p(1) have "A $$ (i,j) - C $$ (i,j) \<succ> B $$ (i,j)"
    by (metis add.commute add_diff_cancel_right' add_uminus_conv_diff plus_gt_right_mono)
  ultimately show "A - C >\<^sub>m B" using mat_gt_def ij_p assms(3) by auto
next
  assume as: "A - C >\<^sub>m B"
  then obtain i j where ij_p: "A $$ (i,j) - C $$ (i,j) \<succ> B $$ (i,j)" "i < n" "j < n"
    using mat_gt_def mat_minus_compo_alt assms(2,3) by auto
  from as have "A - C \<ge>\<^sub>m B" by auto
  then have "A \<ge>\<^sub>m B + C"
    using mat_cmp_minus_eq assms by auto
  moreover
  from ij_p(1) have "A $$ (i,j) \<succ> B $$ (i,j) + C $$ (i,j)" 
    by (metis add.commute add_diff_cancel_right' add_uminus_conv_diff plus_gt_right_mono)
  ultimately show "A >\<^sub>m B + C" using mat_gt_def ij_p assms(3) by auto
qed

lemma mat_minus_cmp:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
  shows "A + B >\<^sub>m C \<longleftrightarrow> A >\<^sub>m C - B"
proof 
  assume as: "A + B >\<^sub>m C"
  then obtain i j where ij_p: "A $$ (i,j) + B $$ (i,j) \<succ> C $$ (i,j)" "i < n" "j < n"
    using mat_gt_def mat_add_compo_alt assms(2,3) by auto
  from as have "A + B \<ge>\<^sub>m C" by auto
  then have "A \<ge>\<^sub>m C - B"
    using mat_minus_cmp_eq assms by auto
  moreover
  from ij_p have "A $$ (i,j) \<succ> C $$ (i,j) - B $$ (i,j)" 
    by (metis add.commute add_diff_cancel_right' add_uminus_conv_diff plus_gt_right_mono)
  ultimately show "A >\<^sub>m C - B" using mat_gt_def ij_p assms(2) by auto
next
  assume as: "A >\<^sub>m C - B"
  then obtain i j where ij_p: "A $$ (i,j) \<succ> C $$ (i,j) - B $$ (i,j)" "i < n" "j < n"
    using mat_gt_def mat_minus_compo_alt assms(2,3) by auto
  from as have "A \<ge>\<^sub>m C - B" by auto
  then have "A + B \<ge>\<^sub>m C"
    using mat_minus_cmp_eq assms by auto
  moreover
  from ij_p have "A $$ (i,j) + B $$ (i,j) \<succ> C $$ (i,j)" 
    by (metis add.commute add_diff_cancel_right' add_uminus_conv_diff plus_gt_right_mono)
  ultimately show "A + B >\<^sub>m C" using mat_gt_def ij_p assms(2) by auto
qed

lemma mat_comparison_zero: 
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  shows "A >\<^sub>m B = (A - B >\<^sub>m 0\<^sub>m n n)"
  using assms mat_cmp_minus[of A "0\<^sub>m n n"] left_add_zero_mat by auto

lemma mat_comparison_imp_nonnull_diff:
  assumes "(A :: 'a mat) \<in> carrier_mat n n" "B \<in> carrier_mat n n" "A >\<^sub>m B"
  shows "\<exists>C. C >\<^sub>m 0\<^sub>m n n \<and> A = B + C"
proof
  have "A - B >\<^sub>m 0\<^sub>m n n" using mat_comparison_zero[OF assms(1,2)] assms(3) by auto
  moreover
  have "B + (A - B) = A"
    using uminus_l_inv_mat[OF assms(2)] add_uminus_minus_mat[symmetric, OF assms(1,2)]
          assms(1,2) by auto
  ultimately show "A - B >\<^sub>m 0\<^sub>m n n \<and> A = B + (A - B)" by auto
qed



text \<open>Transitivity of comparisons made simpler\<close>


lemma mat_gt_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B" "B >\<^sub>m C"
        shows "A >\<^sub>m C"
  using assms by (meson ge_refl mat_gt_trans)

lemma mat_ge_gt_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A \<ge>\<^sub>m B" "B >\<^sub>m C"
        shows "A >\<^sub>m C"
  by (meson assms(1,2,4,5) ge_refl mat_ge_gt_trans)

lemma mat_gt_ge_trans_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B" "B \<ge>\<^sub>m C"
        shows "A >\<^sub>m C"
  by (meson assms(1,2,4,5) ge_refl mat_gt_ge_trans)


text \<open>Monotonicity of comparisons made simpler\<close>

lemma mat_gt_add_left_mono_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B"
        shows "A + C >\<^sub>m B + C"
  by (meson assms(1,2,3,4) mat_plus_gt_left_mono order_refl)

lemma mat_gt_add_right_mono_simpler:
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "C \<in> carrier_mat n n"
          "A >\<^sub>m B"
        shows "C + A >\<^sub>m C + B"
  using assms mat_gt_add_left_mono_simpler by (simp add: comm_add_mat)


text \<open>SN of matrix strict comparison\<close>


definition mat_gt_set :: "('a mat * 'a mat) set" where
"mat_gt_set = {(a,b). a \<in> carrier_mat n n \<and> b \<in> carrier_mat n n \<and>
                      a \<ge>\<^sub>m 0\<^sub>m n n \<and> b \<ge>\<^sub>m 0\<^sub>m n n \<and> a >\<^sub>m b}"

lemma SN_mat_gt: "SN mat_gt_set"
  unfolding mat_gt_set_def using mat_gt_SN[OF le_refl, of n] by fastforce
end

subsection \<open>Notations for elements in $A^* $ where $A$ is some set of matrices.
 Note that the usual relation closures cannot be used here to faithfully
 represent the multiplications going on.\<close>

context squared_ring_mat
begin
fun prod_list_mat :: "'a mat list \<Rightarrow> 'a mat" where
  "prod_list_mat [] = 1\<^sub>m n"
| "prod_list_mat (x#xs) = x * prod_list_mat xs"





lemma prod_list_mat_closed:
  assumes "submonoid A interp_mul_monoid_mat" "set a\<^sub>1 \<subseteq> A"
shows "prod_list_mat a\<^sub>1 \<in> A"
  using assms(2)
proof (induction a\<^sub>1)
  case Nil
  then show ?case using assms(1)[unfolded submonoid_def interp_mul_monoid_mat_def] by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    from Cons.prems have "set a\<^sub>1 \<subseteq> A" by auto
    then have "prod_list_mat a\<^sub>1 \<in> A" using Cons.IH by auto
    moreover
    have "prod_list_mat (a # a\<^sub>1) = a * prod_list_mat a\<^sub>1" by auto
    moreover
    have "a \<in> A" using Cons.prems by auto
    ultimately show "prod_list_mat (a # a\<^sub>1) \<in> A"
      using assms(1)[unfolded submonoid_def interp_mul_monoid_mat_def] by auto
  qed
qed


lemma prod_list_mat_singleton[simp]:
  assumes "x \<in> carrier_mat n n"
  shows "prod_list_mat[x] = x"
proof -
  have "prod_list_mat[x] = x * prod_list_mat []" by auto
  also have "\<dots> = x * 1\<^sub>m n" by auto
  also have "\<dots> = x" using assms by auto
  finally show ?thesis.
qed

lemma prod_list_mat_mult:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
  shows "prod_list_mat (a\<^sub>1@a\<^sub>2) = prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using prod_list_mat.simps(1) left_mult_one_mat prod_list_mat_closed[of "carrier_mat n n" a\<^sub>2]
          assms(2) subset_trans mul_monoid_mat_is_submonoid
    by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    have "set a\<^sub>1 \<subseteq> carrier_mat n n" using Cons.prems by auto
    then have ih: "prod_list_mat (a\<^sub>1 @ a\<^sub>2) = prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2"
      using Cons.IH by auto
    have "prod_list_mat (a#a\<^sub>1@a\<^sub>2) = a * prod_list_mat (a\<^sub>1@a\<^sub>2)" by auto
    also have "\<dots> = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
      using ih by auto
    moreover
    have "prod_list_mat (a#a\<^sub>1) * prod_list_mat a\<^sub>2 = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
    proof -
      have carr:"a \<in> carrier_mat n n"
                "prod_list_mat a\<^sub>1 \<in> carrier_mat n n"
                "prod_list_mat a\<^sub>2 \<in> carrier_mat n n"
        using Cons.prems prod_list_mat_closed mul_monoid_mat_is_submonoid assms(2)
        by auto
      have "prod_list_mat (a#a\<^sub>1) * prod_list_mat a\<^sub>2 = (a * prod_list_mat a\<^sub>1) * prod_list_mat a\<^sub>2"
        by auto
      also have "\<dots> = a * (prod_list_mat a\<^sub>1 * prod_list_mat a\<^sub>2)"
        using carr
        by (rule assoc_mult_mat)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
qed



lemma prod_list_mat_mult_map:
  assumes "set (map f a\<^sub>1) \<subseteq> carrier_mat n n" "set (map f a\<^sub>2) \<subseteq> carrier_mat n n"
  shows "prod_list_mat (map f (a\<^sub>1@a\<^sub>2)) = (prod_list_mat (map f a\<^sub>1)) * (prod_list_mat (map f a\<^sub>2))"
  using assms map_append prod_list_mat_mult
  by auto



lemma prod_list_mat_assoc_left:
  assumes "set a \<subseteq> carrier_mat n n" and xy_carr: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
  shows "prod_list_mat a * x + prod_list_mat a * y = prod_list_mat a * (x + y)"
  by (rule mult_add_distrib_mat[OF prod_list_mat_closed[OF mul_monoid_mat_is_submonoid assms(1)] assms(2,3), symmetric])

lemma prod_list_mat_assoc_right:
  assumes "set a \<subseteq> carrier_mat n n" and xy_carr: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
  shows "x * prod_list_mat a + y * prod_list_mat a = (x + y) * prod_list_mat a"
  by (rule add_mult_distrib_mat[OF assms(2,3) prod_list_mat_closed[OF mul_monoid_mat_is_submonoid assms(1)], symmetric])


subsection \<open>Same idea as above but with addition\<close>

fun add_list_mat :: "'a mat list \<Rightarrow> 'a mat" where
  "add_list_mat [] = 0\<^sub>m n n"
| "add_list_mat (x#xs) = x + add_list_mat xs"


lemma add_list_mat_closed:
  assumes "submonoid A interp_add_monoid_mat" "set a\<^sub>1 \<subseteq> A"
  shows "add_list_mat a\<^sub>1 \<in> A"
  using assms(2)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using assms(1)[unfolded submonoid_def interp_add_monoid_mat_def monoid_mat_def] by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    from Cons.prems have "set a\<^sub>1 \<subseteq> A" by auto
    then have "add_list_mat a\<^sub>1 \<in> A" using Cons.IH by auto
    moreover
    have "add_list_mat (a # a\<^sub>1) = a + add_list_mat a\<^sub>1" by auto
    moreover
    have "a \<in> A" using Cons.prems by auto
    ultimately show "add_list_mat (a # a\<^sub>1) \<in> A"
      using assms(1)[unfolded submonoid_def interp_add_monoid_mat_def monoid_mat_def] by auto
  qed
qed

lemma add_list_mat_singleton[simp]:
  assumes "x \<in> carrier_mat n n"
  shows "add_list_mat[x] = x"
proof -
  have "add_list_mat[x] = x + add_list_mat []" by auto
  also have "\<dots> = x + 0\<^sub>m n n" by auto
  also have "\<dots> = x" using assms by auto
  finally show ?thesis.
qed


lemma add_list_mat_add:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
  shows "add_list_mat (a\<^sub>1@a\<^sub>2) = add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case
    using add_list_mat.simps(1) left_add_zero_mat add_list_mat_closed[of "carrier_mat n n" a\<^sub>2]
          assms(2) subset_trans add_monoid_mat_is_submonoid
    by auto
next
  case (Cons a a\<^sub>1)
  then show ?case
  proof -
    have "set a\<^sub>1 \<subseteq> carrier_mat n n" using Cons.prems by auto
    then have ih: "add_list_mat (a\<^sub>1 @ a\<^sub>2) = add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2"
      using Cons.IH by auto
    have "add_list_mat (a#a\<^sub>1@a\<^sub>2) = a + add_list_mat (a\<^sub>1@a\<^sub>2)" by auto
    also have "\<dots> = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
      using ih by auto
    moreover
    have "add_list_mat (a#a\<^sub>1) + add_list_mat a\<^sub>2 = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
    proof -
      have carr:"a \<in> carrier_mat n n"
                "add_list_mat a\<^sub>1 \<in> carrier_mat n n"
                "add_list_mat a\<^sub>2 \<in> carrier_mat n n"
        using Cons.prems add_list_mat_closed add_monoid_mat_is_submonoid assms(2)
        by auto
      have "add_list_mat (a#a\<^sub>1) + add_list_mat a\<^sub>2 = (a + add_list_mat a\<^sub>1) + add_list_mat a\<^sub>2"
        by auto
      also have "\<dots> = a + (add_list_mat a\<^sub>1 + add_list_mat a\<^sub>2)"
        using carr
        by (rule assoc_add_mat)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
qed


lemma add_list_mat_add_map:
  assumes "set (map f a\<^sub>1) \<subseteq> carrier_mat n n" "set (map f a\<^sub>2) \<subseteq> carrier_mat n n"
  shows "add_list_mat (map f (a\<^sub>1@a\<^sub>2)) = (add_list_mat (map f a\<^sub>1)) + (add_list_mat (map f a\<^sub>2))"
  using assms map_append add_list_mat_add
  by auto


lemma add_list_mat_distrib:
  assumes "set a\<^sub>1 \<subseteq> carrier_mat n n" "a \<in> carrier_mat n n"
  shows "a * add_list_mat a\<^sub>1 = add_list_mat (map (\<lambda>x. a * x) a\<^sub>1)"
  using assms(1)
proof (induction a\<^sub>1)
  case Nil
  then show ?case using list.map(1) add_list_mat.simps(1) right_mult_zero_mat assms(2) by auto
next
  case (Cons x xs)
  then show ?case
  proof -
    have carr: "x \<in> carrier_mat n n" "set xs \<subseteq> carrier_mat n n"
      using Cons.prems by auto
    then have "a * add_list_mat (x # xs) = a * (x + add_list_mat xs)"
      using add_list_mat_add add_list_mat_singleton
      by auto
    also have "\<dots> = a * x + a * add_list_mat xs"
      using mult_add_distrib_mat carr assms(2)
            add_list_mat_closed[of "carrier_mat n n" xs]
            add_monoid_mat_is_submonoid
      by auto
    moreover
    have "add_list_mat (map ((*) a) (x # xs)) = add_list_mat (map ((*) a) [x]) +
                                                add_list_mat (map ((*) a) xs)"
      using add_list_mat_add_map[of _ "[x]" xs] carr assms(2) mult_carrier_mat
      by auto
    moreover
    have "add_list_mat (map ((*) a) [x]) + add_list_mat (map ((*) a) xs) =
           a * x + add_list_mat (map ((*) a) xs)"
      using add_list_mat_singleton carr(1) assms(2) mult_carrier_mat
      by auto
    moreover
    have "a * x + add_list_mat (map ((*) a) xs) = a * x + a * add_list_mat xs"
      using Cons.IH Cons.prems by auto
    ultimately show ?thesis by auto
  qed
qed


subsection \<open>Positive and strictly positive cones\<close>

text \<open>Defining the positive cone $N$ for a ring of matrices\<close>

definition N :: "'a mat set" where
  "N = {A. A \<in> carrier_mat n n \<and> A \<ge>\<^sub>m 0\<^sub>m n n}"

lemma N_in_carr[simp]: "N \<subseteq> carrier_mat n n"
  using N_def by auto

lemma N_el_in_carr:
  assumes "x \<in> N"
  shows "x \<in> carrier_mat n n"
  using assms N_in_carr in_mono[of N "carrier_mat n n"] by auto

text \<open>Alternative definitions\<close>

lemma N_greater_eq_zero: 
  assumes "A \<in> carrier_mat n n"
  shows "A \<in> N = (A \<ge>\<^sub>m 0\<^sub>m n n)"
  using assms N_def by auto

lemma N_compo_greater_eq_zero:
  assumes "A \<in> N" "i < n" "j < n"
  shows "A $$ (i, j) \<ge> 0"
  using assms N_el_in_carr[of A] N_greater_eq_zero[of A] mat_ge_def by auto


lemma N_compo_greater_eq_zero2: "A \<in> N =
 (A \<in> carrier_mat n n \<and> (\<forall>i j. i < n \<longrightarrow> j < n \<longrightarrow> A $$ (i, j) \<ge> 0))"
  unfolding N_def
  using mat_ge_def index_zero_mat(1)
  by auto

lemma zero_in_N[simp]: "0\<^sub>m n n \<in> N"
  using N_greater_eq_zero by (auto simp: ge_refl)

lemma one_in_N[simp]: "1\<^sub>m n \<in> N"
  using N_greater_eq_zero by (auto simp: one_ge_zero ge_refl)





text \<open>Positive cone is closed under multiplication and addition\<close>

lemma N_mult_closed:
  assumes "A \<in> N" "B \<in> N"
  shows "A * B \<in> N"
proof -
  have "B \<ge>\<^sub>m 0\<^sub>m n n" using assms(2) N_greater_eq_zero N_el_in_carr by auto
  then have "A * B \<ge>\<^sub>m 0\<^sub>m n n * B"
    using assms N_greater_eq_zero[of A] N_el_in_carr
          mat_mult_left_mono[of B n A "0\<^sub>m n n"]
          zero_carrier_mat[of n n]
    by auto
  then show ?thesis
    using left_mult_zero_mat[of B n n n]
          N_greater_eq_zero[of "A * B"]
          assms N_el_in_carr mult_carrier_mat[of A n n B n]
    by auto
qed


lemma N_add_closed:
  assumes "A \<in> N" "B \<in> N"
  shows "A + B \<in> N"
proof -
  have ABcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
    using assms N_el_in_carr by auto
  then have "A + B \<in> carrier_mat n n"
    using add_carrier_mat by auto
  moreover
  {
    fix i j
    assume ij_p: "i < n" "j < n"
    then have "A $$ (i,j) \<ge> 0" "B $$ (i,j) \<ge> 0"
      using assms N_compo_greater_eq_zero2 by auto
    moreover
    from ij_p have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt ABcarr by auto
    ultimately have "(A + B) $$ (i,j) \<ge> 0"
      by (metis add.right_neutral plus_mono)
  }
  ultimately show ?thesis using N_compo_greater_eq_zero2[symmetric, of "A + B"] by auto
qed
    

lemma prod_list_mat_in_N:
  assumes "set a \<subseteq> N"
  shows "prod_list_mat a \<in> N"
  using assms
proof (induction a)
  case Nil
  then show ?case using prod_list_mat.simps(1) N_greater_eq_zero by auto
next
  case (Cons a\<^sub>1 a\<^sub>2)
  then show ?case
  proof -
    have "prod_list_mat (a\<^sub>1 # a\<^sub>2) = a\<^sub>1 * prod_list_mat a\<^sub>2" by auto
    moreover
    have "a\<^sub>1 \<in> N" using Cons.prems by auto
    moreover
    have "prod_list_mat a\<^sub>2 \<in> N" using Cons.prems by (simp add: Cons.IH)
    ultimately show ?thesis using N_mult_closed by auto
  qed
qed



lemma N_is_submonoid_mul: "submonoid N interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using N_in_carr by simp
next
  case (2 x y)
  then show ?case using N_mult_closed by simp
next
  case 3
  then show ?case using one_in_N by simp
qed

lemma N_is_submonoid_add: "submonoid N interp_add_monoid_mat"
  using N_add_closed zero_in_N
  by (unfold_locales, unfold interp_add_monoid_mat_def monoid_mat_def, auto)



text \<open>Defining the strictly positive cone $P$ for a ring of matrices\<close>

definition P :: "'a mat set" where
  "P = {A. A \<in> carrier_mat n n \<and> A >\<^sub>m 0\<^sub>m n n}"

lemma P_in_carr[simp]: "P \<subseteq> carrier_mat n n"
  using P_def by auto

lemma P_el_in_carr:
  assumes "x \<in> P"
  shows "x \<in> carrier_mat n n"
  using assms P_in_carr in_mono[of P "carrier_mat n n"] by auto





text \<open>Alternative definitions\<close>

lemma P_greater_zero:
  assumes "A \<in> carrier_mat n n"
  shows "A \<in> P = (A >\<^sub>m 0\<^sub>m n n)"
  using assms P_def by auto

lemma P_N_one_elem_nonnull:
  assumes "A \<in> N"
  shows "A \<in> P = (\<exists>i j. i < n \<and> j < n \<and> A $$ (i,j) \<succ> 0)"
  unfolding P_def mat_gt_def
  using assms[unfolded N_def] index_zero_mat(1)[of _ n _ n]
  by fastforce
  

lemma P_in_N: "P \<subseteq> N"
  by (simp only: P_def N_def) auto
end

context squared_ring_mat_with_assms
begin

lemma gt_irrefl[simp]: "x \<ge> 0 \<Longrightarrow> \<not> x \<succ> x" using SN by fast

lemma zero_not_in_P: "0\<^sub>m n n \<notin> P"
  using P_def by (auto simp: mat_gt_def) 



lemma P_add_closed:
  assumes "A \<in> P" "B \<in> N"
  shows "A + B \<in> P"
proof -
  have ABcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
    using assms P_el_in_carr N_el_in_carr by auto
  then have add_carr: "A + B \<in> carrier_mat n n"
    using add_carrier_mat by auto
  moreover
  have "A + B >\<^sub>m 0\<^sub>m n n"
  proof -
    have "A + B \<ge>\<^sub>m 0\<^sub>m n n"
      using assms N_add_closed set_mp[OF P_in_N] N_greater_eq_zero[OF add_carr]
      by auto
    moreover
    {
      obtain i j where ij_p: "i < n" "j < n" "A $$ (i,j) \<succ> 0"
        using assms[unfolded P_def] by auto
      moreover have "B $$ (i,j) \<ge> 0"
        using calculation assms(2) N_compo_greater_eq_zero by auto
      ultimately
      have "A $$ (i,j) + B $$ (i,j) \<succ> 0" 
        by (metis add_0 compat2 plus_gt_left_mono)
      then have "(A + B) $$ (i,j) \<succ> 0"
        using index_add_mat(1) ij_p ABcarr by auto
      then have "\<exists>i j. i < n \<and> j < n \<and> (A + B) $$ (i,j) \<succ> 0" using ij_p by auto
    }
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis using P_greater_zero by auto
qed

subsection \<open>Core of a set\<close>
context
begin

text \<open>$core(A)$ is defined such that $A^*core(A)A^* \subseteq P$.
 Typically, we want the interpretation of the alphabet to be in $A$ and
 the interpretation of the rules of an SRS to be in $core(A)$.\<close>

definition core :: "'a mat set \<Rightarrow> 'a mat set" where
 "core A = {d. d \<in> carrier_mat n n \<and>
   (\<forall>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> A \<and> set a\<^sub>2 \<subseteq> A \<longrightarrow>
    ( prod_list_mat a\<^sub>1 * d * prod_list_mat a\<^sub>2 ) \<in> P
    )
  }"


lemma core_def_alt: "x \<in> core A =
 (x \<in> carrier_mat n n \<and>
 (\<forall>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> A \<longrightarrow> set a\<^sub>2 \<subseteq> A \<longrightarrow> prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P))"
  unfolding core_def by auto


lemma core_in_carr[simp]: "core A \<subseteq> carrier_mat n n"
  using core_def by auto

lemma core_el_in_carr:
  assumes "x \<in> core A"
  shows "x \<in> carrier_mat n n"
  using core_in_carr in_mono[of "core A" "carrier_mat n n" x] assms by auto


lemma core_element_in_P:
  assumes Acarr: "A \<subseteq> carrier_mat n n" and
    xA: "x \<in> core A" and lA: "l \<in> A" and rA: "r \<in> A"
  shows "l * x * r \<in> P"
proof -
  from xA[unfolded core_def, simplified] have x: "x \<in> carrier_mat n n"
  and inP: "set a\<^sub>1 \<subseteq> A \<Longrightarrow> set a\<^sub>2 \<subseteq> A \<Longrightarrow> prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P" for a\<^sub>1 a\<^sub>2
    by auto
  moreover
  from inP[of "[l]" "[r]"] lA rA 
  have "prod_list_mat [l] * x * prod_list_mat [r] \<in> P" by auto
  moreover
  from lA Acarr have "l \<in> carrier_mat n n" by auto
  moreover
  from rA Acarr have "r \<in> carrier_mat n n" by auto
  ultimately show "l * x * r \<in> P" using prod_list_mat_singleton by auto
qed

lemma core_element_gt:
  assumes "A \<subseteq> carrier_mat n n" "x \<in> core A" "l \<in> A" "r \<in> A"
  shows "l * x * r >\<^sub>m 0\<^sub>m n n"
  using core_element_in_P P_greater_zero assms P_el_in_carr
  by meson

lemma core_extended:
  assumes "A \<subseteq> carrier_mat n n" "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A" "x \<in> core A"
  shows "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> core A"
proof -

  have "x \<in> carrier_mat n n" using assms(4) core_el_in_carr by auto


  have "\<And>u v. set u \<subseteq> A \<Longrightarrow> set v \<subseteq> A \<Longrightarrow>
         prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v \<in> P"
  proof -
    fix u v
    assume suv_p: "set u \<subseteq> A" "set v \<subseteq> A"
    then obtain a3 a4  where
                           a_p:   "a3 = u@a\<^sub>1" "a4 = a\<^sub>2@v"
                      and  sa_p:  "set a3 \<subseteq> A" "set a4 \<subseteq> A"
      using assms(2) assms(3) by auto
    
    have st1: "prod_list_mat a3 * x * prod_list_mat a4 \<in> P" using sa_p core_def assms(4) by auto
    then have "prod_list_mat a3 * x * prod_list_mat a4 =
              (prod_list_mat u * prod_list_mat a\<^sub>1) * x * (prod_list_mat a\<^sub>2 * prod_list_mat v)"
      using prod_list_mat_mult assms(1) a_p suv_p sa_p  by auto
    also have "\<dots> = prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v"
      using mat_mult_assoc_5[of "prod_list_mat u" "prod_list_mat a\<^sub>1"]
            \<open>x \<in> carrier_mat n n\<close> prod_list_mat_closed mul_monoid_mat_is_submonoid
            suv_p assms(1,2,3)
      by auto
    finally
    show "prod_list_mat u * (prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2) * prod_list_mat v \<in> P"
      using st1
      by auto
  qed
  then show ?thesis using assms by (simp add: P_el_in_carr core_def)
qed


lemma core_in_P: "core A \<subseteq> P"
proof
  fix x
  assume "x \<in> core A"
  then obtain a\<^sub>1 a\<^sub>2 where "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A" and a_empty: "a\<^sub>1 = []" "a\<^sub>2 = []"
                    and in_p: "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P"
    using core_def_alt[of x A] core_el_in_carr[of x A]
    by (metis empty_iff empty_set subset_iff)

  then show "x \<in> P"
    using \<open>x \<in> core A\<close> core_el_in_carr[of x A] prod_list_mat.simps(1)
          left_mult_one_mat[of x n n] right_mult_one_mat[of x n n]
    by auto
qed


lemma core_gt:
  assumes "x \<in> carrier_mat n n" "y \<in> carrier_mat n n" "x - y \<in> core A"
  shows "x >\<^sub>m y"
  using mat_comparison_zero[OF assms(1,2)]
        P_greater_zero[OF set_mp[OF subset_trans[OF core_in_P P_in_carr] assms(3)]]
        set_mp[OF core_in_P assms(3)]
  by auto



lemma core_plus_mono:
  assumes "A \<subseteq> carrier_mat n n" "x \<in> core A" "y \<in> core A"
  shows "x + y \<in> core A"
proof -
  have carrs: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
    using assms core_el_in_carr by auto
  {
    fix a\<^sub>1 a\<^sub>2
    assume as: "set a\<^sub>1 \<subseteq> A" "set a\<^sub>2 \<subseteq> A"
    then have xy_p: "prod_list_mat a\<^sub>1 * x * prod_list_mat a\<^sub>2 \<in> P" (is "?left \<in> _")
                    "prod_list_mat a\<^sub>1 * y * prod_list_mat a\<^sub>2 \<in> P" (is "?right \<in> _")
      using assms[unfolded core_def] by auto
    have carrs2: "set a\<^sub>1 \<subseteq> carrier_mat n n" "set a\<^sub>2 \<subseteq> carrier_mat n n"
                 "prod_list_mat a\<^sub>1 \<in> carrier_mat n n" "prod_list_mat a\<^sub>2 \<in> carrier_mat n n"
      using as assms(1) prod_list_mat_closed[OF mul_monoid_mat_is_submonoid] by auto

    have "?left + ?right = (prod_list_mat a\<^sub>1 * x + prod_list_mat a\<^sub>1 * y) * prod_list_mat a\<^sub>2"
      using prod_list_mat_assoc_right[OF carrs2(2)] mult_carrier_mat[OF carrs2(3)] carrs
      by auto
    also have "\<dots> = prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2"
      using prod_list_mat_assoc_left[OF carrs2(1)] carrs by auto
    finally have "?left + ?right = prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2".
    moreover
    have "?left + ?right \<in> P" using P_add_closed[OF xy_p(1) set_mp[OF P_in_N xy_p(2)]].
    ultimately
    have "prod_list_mat a\<^sub>1 * (x + y) * prod_list_mat a\<^sub>2 \<in> P"
      using carrs by auto
  }
  then show ?thesis unfolding core_def using add_carrier_mat carrs(2) by blast
qed


lemma core_plus_N_mono:
  assumes "A \<subseteq> N" "x \<in> core A" "y \<in> N"
  shows "x + y \<in> core A"
proof -
  have carrs: "x \<in> carrier_mat n n" "y \<in> carrier_mat n n"
    using assms core_el_in_carr N_el_in_carr by auto
  {
    fix a1 a2
    assume a_p: "set a1 \<subseteq> A" "set a2 \<subseteq> A"
    then have a_p2: "set a1 \<subseteq> N" "set a1 \<subseteq> carrier_mat n n"
                    "set a2 \<subseteq> N" "set a2 \<subseteq> carrier_mat n n"
      using assms N_in_carr set_mp by blast+

    from a_p have x_p: "prod_list_mat a1 * x * prod_list_mat a2 \<in> P"
      using assms[unfolded core_def] by auto

    have carrs2: "prod_list_mat a1 \<in> carrier_mat n n" "prod_list_mat a2 \<in> carrier_mat n n"
      using prod_list_mat_closed[OF mul_monoid_mat_is_submonoid] a_p2
      by auto

    have "prod_list_mat a1 * (x + y) * prod_list_mat a2 =
           (prod_list_mat a1 * x + prod_list_mat a1 * y) * prod_list_mat a2"
      using prod_list_mat_assoc_left[OF a_p2(2) carrs] by auto
    then have "prod_list_mat a1 * (x + y) * prod_list_mat a2 =
      prod_list_mat a1 * x * prod_list_mat a2 + prod_list_mat a1 * y * prod_list_mat a2"
      using prod_list_mat_assoc_right[OF a_p2(4) mult_carrier_mat[OF carrs2(1)] mult_carrier_mat[OF carrs2(1)]]
            carrs
      by auto
    moreover
    have "prod_list_mat a1 * x * prod_list_mat a2 + prod_list_mat a1 * y * prod_list_mat a2 \<in> P"
    proof -

      have "prod_list_mat a1 * y * prod_list_mat a2 \<in> N"
        using prod_list_mat_closed[OF N_is_submonoid_mul] a_p2(1,3) assms(3) N_mult_closed
        by auto
      then show ?thesis using x_p P_add_closed by auto
    qed
    ultimately
    have "prod_list_mat a1 * (x + y) * prod_list_mat a2 \<in> P" by auto
  }
  then show ?thesis unfolding core_def using add_carrier_mat carrs(2) by blast
qed



end (*Core of a set*)
end

section \<open>Matrix sets of interest\<close>
context squared_ring_mat
begin
definition E\<^sub>I :: "nat set \<Rightarrow> 'a mat set" where
  "E\<^sub>I I = {d \<in> N. \<forall>i \<in> I. d $$ (i,i) \<ge> 1}"

definition P\<^sub>I :: "nat set \<Rightarrow> 'a mat set" where
  "P\<^sub>I I = {d \<in> N. \<exists>i \<in> I. \<exists>j \<in> I. d $$ (i,j) \<succ> 0}"

definition M\<^sub>I :: "nat set \<Rightarrow> 'a mat set" where
  "M\<^sub>I I = {d \<in> N. \<forall>i \<in> I. \<exists>j \<in> I. d $$ (i,j) \<ge> 1}"

definition L\<^sub>I :: "nat set \<Rightarrow> 'a mat set" where
  "L\<^sub>I I = {d \<in> N. \<forall>i \<in> I. \<exists>j \<in> I. d $$ (i,j) \<succ> 0}"

end

context squared_ring_mat_with_assms
begin

context
  fixes I
  assumes I0: "I \<subseteq> {..< n}" 
  and I_non_empty: "I \<noteq> {}" 
begin



lemma one_in_E\<^sub>I[simp]: "1\<^sub>m n \<in> E\<^sub>I I"
proof -
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "(1\<^sub>m n) $$ (i,i) \<ge> (1 :: 'a)" using index_one_mat(1) by (auto simp: ge_refl)
  }
  then show ?thesis unfolding E\<^sub>I_def using one_in_N by auto
qed

lemma E\<^sub>I_in_N[simp]: "E\<^sub>I I \<subseteq> N"
  using E\<^sub>I_def by auto


lemma E\<^sub>I_in_carr[simp]: "E\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "E\<^sub>I I" N "carrier_mat n n"] E\<^sub>I_in_N N_in_carr by auto


lemma E\<^sub>I_el_in_carr:
  assumes "x \<in> E\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms E\<^sub>I_in_carr in_mono[of "E\<^sub>I I" "carrier_mat n n"] by auto




lemma E\<^sub>I_el_in_N:
  assumes "x \<in> E\<^sub>I I"
  shows "x \<in> N"
  using assms E\<^sub>I_in_N in_mono[of "E\<^sub>I I" N] by auto


lemma E\<^sub>I_greater_zero:
  assumes "x \<in> E\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from I_non_empty obtain i where "i \<in> I" by auto
  with assms[unfolded E\<^sub>I_def] have "x $$ (i, i) \<ge> 1" by auto
  with one_gt_zero have "x $$ (i, i) \<succ> 0" by (metis compat)
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from assms E\<^sub>I_el_in_carr[of x] E\<^sub>I_el_in_N[of x] N_greater_eq_zero[of x]
    have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto 
  ultimately show ?thesis by auto
qed


lemma E\<^sub>I_in_P: "E\<^sub>I I \<subseteq> P"
  using E\<^sub>I_greater_zero E\<^sub>I_el_in_carr P_greater_zero by auto


lemma E\<^sub>I_mult_id_left:
  assumes "A \<in> E\<^sub>I I"
  shows "1\<^sub>m n * A \<in> E\<^sub>I I"
proof -
  have "1\<^sub>m n * A = A"
    using left_mult_one_mat E\<^sub>I_el_in_carr assms
    by auto
  then show ?thesis using assms by auto
qed

lemma E\<^sub>I_mult_id_right:
  assumes "A \<in> E\<^sub>I I"
  shows "A * 1\<^sub>m n \<in> E\<^sub>I I"
proof -
  have "A * 1\<^sub>m n = A"
    using right_mult_one_mat E\<^sub>I_el_in_carr assms
    by auto
  then show ?thesis using assms by auto
qed

lemma E\<^sub>I_closed_mult:
  assumes "A \<in> E\<^sub>I I" "B \<in> E\<^sub>I I"
  shows "A * B \<in> E\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> (A * B) $$ (i, i) \<ge> 1"
  proof -
    fix i
    assume as1: "i \<in> I"
    have "i < n" using I0 as1 by auto
    moreover
    have triv1: "A $$ (i, i) \<ge> 1" using assms(1) as1 by (simp add: E\<^sub>I_def)
    have triv2: "B $$ (i, i) \<ge> 1" using assms(2) as1 by (simp add: E\<^sub>I_def)
    have A_carr: "A \<in> carrier_mat n n" using E\<^sub>I_el_in_carr[of A] assms(1) by auto
    have B_carr: "B \<in> carrier_mat n n" using E\<^sub>I_el_in_carr[of B] assms(2) by auto
    have st1: "(A * B) $$ (i,i) = (\<Sum> k \<in> {..< n}. A $$ (i,k) * B $$ (k,i))"
      using A_carr B_carr \<open>i < n\<close> mat_mult_compo_alt
      by blast
    have "A $$ (i,i) * B $$ (i,i) \<ge> 1"
      using triv1 triv2 E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B]
      by auto
    moreover
    have "\<And>k. k \<in> {..< n} \<Longrightarrow> A $$ (i,k) * B $$ (k,i) \<ge> 0"
      using \<open>i < n\<close> assms E\<^sub>I_el_in_N[of A] E\<^sub>I_el_in_N[of B]
            A_carr B_carr
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ i]
            mult_nonneg_nonneg[of "A $$ (i, _)" "B $$ (_, i)"]
      by auto
    ultimately have "(A * B) $$ (i, i) \<ge> 1 + 0" unfolding st1 
      by (subst sum.remove[of _ i], force, force, intro plus_mono sum_nonneg, auto)
    thus "(A * B) $$ (i, i) \<ge> 1" by auto
  qed
  
  moreover
  have "A * B \<in> carrier_mat n n"
    using assms E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B] mult_carrier_mat[of A n n B n]
    by auto
  moreover
  from mat_mult_right_mono[of A n B "0\<^sub>m n n"] right_mult_zero_mat[of A n n n]
      E\<^sub>I_el_in_carr[of A] E\<^sub>I_el_in_carr[of B] E\<^sub>I_el_in_N[of A] E\<^sub>I_el_in_N[of B]
      N_greater_eq_zero[of A] N_greater_eq_zero[of B] assms
    have "A * B \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis using N_greater_eq_zero[of "A * B"] I0 E\<^sub>I_def by auto
qed



lemma E\<^sub>I_closed_add:
  assumes "A \<in> E\<^sub>I I" "B \<in> N"
  shows "A + B \<in> E\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms E\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "A $$ (i,i) \<ge> 1" "B $$ (i,i) \<ge> 0"
      using assms E\<^sub>I_def N_compo_greater_eq_zero i_p by auto
    moreover
    have "(A + B) $$ (i,i) = A $$ (i,i) + B $$ (i,i)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> by auto
    ultimately have "(A + B) $$ (i,i) \<ge> 1"
      by (simp add: add_increasing2)
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using E\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding E\<^sub>I_def by auto
qed



lemma submonoid_E\<^sub>I: "submonoid (E\<^sub>I I) interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using E\<^sub>I_in_carr by simp
next
  case (2 x y)
  then show ?case using E\<^sub>I_closed_mult by simp
next
  case 3
  then show ?case using one_in_E\<^sub>I by simp
qed



lemma one_in_P\<^sub>I[simp]: "1\<^sub>m n \<in> P\<^sub>I I"
proof -
  obtain i where i_p: "i \<in> I" using I_non_empty by auto
  then have "i < n" using I0 by auto
  then have "(1\<^sub>m n) $$ (i,i) \<succ> (0 :: 'a)" using one_gt_zero by auto
  then have "\<exists>i \<in> I. (1\<^sub>m n) $$ (i,i) \<succ> (0 :: 'a)"
    using i_p by auto
  then show ?thesis unfolding P\<^sub>I_def using one_in_N by auto
qed

lemma P\<^sub>I_in_N[simp]: "P\<^sub>I I \<subseteq> N"
  using P\<^sub>I_def by auto

lemma P\<^sub>I_el_in_N:
  assumes "x \<in> P\<^sub>I I"
  shows "x \<in> N"
  using assms P\<^sub>I_in_N in_mono[of "P\<^sub>I I" N] by auto

lemma P\<^sub>I_in_carr[simp]: "P\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "P\<^sub>I I" N "carrier_mat n n"] P\<^sub>I_in_N N_in_carr by auto

lemma P\<^sub>I_el_in_carr:
  assumes "x \<in> P\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms P\<^sub>I_in_carr in_mono[of "P\<^sub>I I" "carrier_mat n n"] by auto


lemma P\<^sub>I_greater_zero:
  assumes "x \<in> P\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from assms[unfolded P\<^sub>I_def] I_non_empty obtain i j where "i \<in> I" "j \<in> I" "x $$ (i, j) \<succ> 0"
    by auto
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from \<open>j \<in> I\<close> I0 have "j < n" by auto
  moreover
  from assms P\<^sub>I_el_in_N P\<^sub>I_el_in_carr N_greater_eq_zero have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis using I0 mat_gt_def by auto
qed


lemma P\<^sub>I_in_P: "P\<^sub>I I \<subseteq> P"
  using P\<^sub>I_greater_zero P\<^sub>I_el_in_carr P_greater_zero by auto



lemma P\<^sub>I_closed_add:
  assumes "A \<in> P\<^sub>I I" "B \<in> N"
  shows "A + B \<in> P\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms P\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    then obtain i j where ij_p: "i \<in> I" "j \<in> I" "A $$ (i,j) \<succ> 0"
      using assms[unfolded P\<^sub>I_def] by auto
    then have "i < n" "j < n" using ij_p I0 by auto
    then have "B $$ (i,j) \<ge> 0"
      using assms(2) N_compo_greater_eq_zero by auto
    moreover
    have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> \<open>j < n\<close> by auto
    ultimately have "(A + B) $$ (i,j) \<succ> 0"
      by (metis add_0 compat2 ij_p(3) plus_gt_left_mono)
    then have "\<exists>i \<in> I. \<exists>j \<in> I. (A + B) $$ (i,j) \<succ> 0" using ij_p by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using P\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding P\<^sub>I_def by auto
qed



lemma P\<^sub>I_mult_id_left:
  assumes "M \<in> P\<^sub>I I"
  shows "1\<^sub>m n * M \<in> P\<^sub>I I"
proof -
  have "1\<^sub>m n * M = M" using left_mult_one_mat assms P\<^sub>I_el_in_carr
    by auto
  then show ?thesis using assms by auto
qed

lemma P\<^sub>I_mult_id_right:
  assumes "M \<in> P\<^sub>I I"
  shows "M * 1\<^sub>m n \<in> P\<^sub>I I"
proof -
  have "M * 1\<^sub>m n = M" using right_mult_one_mat assms P\<^sub>I_el_in_carr
    by auto
  then show ?thesis using assms by auto
qed

lemma ge_1_mult_pos: assumes "x \<ge> 1" and "y \<succ> 0" 
  shows "x * y \<succ> 0" 
proof -
  define z where "z = x - 1" 
  from assms(1) have z: "z \<ge> 0" unfolding z_def
    by (metis ab_left_minus plus_right_mono uminus_add_conv_diff)
  have "x = 1 + z" unfolding z_def by auto
  also have "\<dots> * y = y + z * y" by (simp add: algebra_simps)
  also have "\<dots> \<ge> y + 0 * 0" 
    by (intro plus_mono ge_refl mult_mono z gt_imp_ge assms)
  finally have "x * y \<ge> y" by simp
  with assms(2) show ?thesis by (metis compat)
qed


lemma P\<^sub>I_closed_E\<^sub>I_mul_left:
  assumes "A \<in> E\<^sub>I I" "B \<in> P\<^sub>I I"
  shows "A * B \<in> P\<^sub>I I"
proof -
  from I0 assms(2) obtain i j where i_prop:  "i \<in> I"
    and j_prop:  "j \<in> I"
    and B_prop: "B $$ (i,j) \<succ> 0"
    by (auto simp: P\<^sub>I_def)

  from assms(1) E\<^sub>I_el_in_carr have triv1: "A \<in> carrier_mat n n" by auto
  from assms(2) P\<^sub>I_el_in_carr have triv2: "B \<in> carrier_mat n n" by auto
  from I0 i_prop have triv3: "i < n" by auto
  from I0 j_prop have triv4: "j < n" by auto

  have res1: "(A * B) $$ (i,j) \<succ> 0"
  proof -
    define f where "f k = A $$ (i, k) * B $$ (k, j)" for k
    from I0 assms(1) i_prop have A_prop: "A $$ (i,i) \<ge> 1" by (simp add: E\<^sub>I_def)
    have id: "(A * B) $$ (i,j) = (\<Sum> k \<in> {..< n}. A $$ (i,k) * B $$ (k,j))"
      using triv1 triv2 triv3 triv4 mat_mult_compo_alt by blast
    from A_prop B_prop have st1:"A $$ (i,i) * B $$ (i,j) \<succ> 0" by (metis ge_1_mult_pos)
    moreover
    from assms E\<^sub>I_el_in_N[of A] P\<^sub>I_el_in_N[of B]
        triv3 triv4 N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j]
        mult_nonneg_nonneg[of "A $$ (i, _)" "B $$ (_, j)"]
    have "\<forall>k \<in> {..< n}. A $$ (i,k) * B $$ (k,j) \<ge> 0" by auto
    moreover
    from st1 triv3 have "\<exists>k \<in> {..< n}. A $$ (i,k) * B $$ (k,j) \<succ> 0" by auto
    ultimately show ?thesis unfolding id f_def[symmetric] using triv3 
      by (meson compat finite_lessThan sum_nonneg_leq_bound)
  qed
  
  from assms(1) assms(2) mat_mult_right_mono[of A n B "0\<^sub>m n n"]
        triv1 triv2 zero_carrier_mat[of n n]
      E\<^sub>I_el_in_N[of A] N_greater_eq_zero[of A] P\<^sub>I_el_in_N[of B] N_greater_eq_zero[of B]
      right_mult_zero_mat[of A n n n]
    have res2: "A * B \<ge>\<^sub>m 0\<^sub>m n n" by (simp add: less_eq_mat_def mat_ge_def)
  from triv1 triv2 mult_carrier_mat[of A n n B n] res2 N_greater_eq_zero[of "A * B"]
    have "A * B \<in> N" by auto
  then show ?thesis unfolding P\<^sub>I_def using res1 i_prop j_prop by auto
qed

lemma P\<^sub>I_closed_E\<^sub>I_mul_right:
  assumes "A \<in> E\<^sub>I I" "B \<in> P\<^sub>I I"
  shows "B * A \<in> P\<^sub>I I"
proof -
  from I0 assms(2) obtain i j where i_prop:  "i \<in> I"
                                      and j_prop:  "j \<in> I"
                                      and B_prop: "B $$ (i,j) \<succ> 0"
    by (simp add: P\<^sub>I_def) auto
  from assms(1) E\<^sub>I_el_in_carr have triv1: "A \<in> carrier_mat n n" by auto
  from assms(2) P\<^sub>I_el_in_carr have triv2: "B \<in> carrier_mat n n" by auto
  from I0 i_prop have triv3: "i < n" by auto
  from I0 j_prop have triv4: "j < n" by auto

  have res1: "(B * A) $$ (i,j) \<succ> 0"
  proof -
    define f where "f k = B $$ (i, k) * A $$ (k, j)" for k
    from assms(1) j_prop have A_prop: "A $$ (j,j) \<ge> 1" by (simp add: E\<^sub>I_def)
    have id: "(B * A) $$ (i,j) = (\<Sum> k \<in> {..< n}. B $$ (i,k) * A $$ (k,j))"
      using triv1 triv2 triv3 triv4 mat_mult_compo_alt by blast
    from A_prop B_prop have st1:"B $$ (i,j) * A $$ (j,j) \<succ> 0"
      by (metis (no_types, opaque_lifting) compat gt_imp_ge mult.right_neutral mult_left_mono)
    moreover
    from assms(1) assms(2) E\<^sub>I_el_in_N[of A] P\<^sub>I_el_in_N[of B]
        triv3 triv4 N_compo_greater_eq_zero[of B i] N_compo_greater_eq_zero[of A _ j]
        mult_nonneg_nonneg[of "B $$ (i, _)" "A $$ (_, j)"]
    have "\<forall>k \<in> {..< n}. B $$ (i,k) * A $$ (k,j) \<ge> 0" by auto
    moreover
    from st1 triv4 have "\<exists>k \<in> {..< n}. B $$ (i,k) * A $$ (k,j) \<succ> 0" by auto
    ultimately show ?thesis unfolding id f_def[symmetric] using triv4
      by (meson compat finite_lessThan sum_nonneg_leq_bound)
  qed

  from assms(1) assms(2) mat_mult_right_mono[of B n A "0\<^sub>m n n"]
      triv1 triv2 zero_carrier_mat[of n n]
      E\<^sub>I_el_in_N[of A] N_greater_eq_zero[of A] P\<^sub>I_el_in_N[of B] N_greater_eq_zero[of B]
      right_mult_zero_mat[of B n n n]
    have res2: "B * A \<ge>\<^sub>m 0\<^sub>m n n" by (simp add: less_eq_mat_def mat_ge_def)
  from triv1 triv2 mult_carrier_mat[of B n n A n] res2 N_greater_eq_zero[of "B * A"]
    have "B * A \<in> N" by auto
  then show ?thesis unfolding P\<^sub>I_def using res1 i_prop j_prop by auto
qed


lemma P\<^sub>I_closed_E\<^sub>I_prod_left:
  assumes "M \<in> P\<^sub>I I" "set a\<^sub>1 \<subseteq> E\<^sub>I I"
  shows "prod_list_mat a\<^sub>1 * M \<in> P\<^sub>I I"
  using assms(2)
proof (cases "a\<^sub>1")
  case Nil
  then show ?thesis
  proof -
    assume as1: "a\<^sub>1 = []"
    then have "prod_list_mat a\<^sub>1 = 1\<^sub>m n" by auto
    then have "prod_list_mat a\<^sub>1 * M = M" using P\<^sub>I_el_in_carr[of M] assms(1) by auto
    then show ?thesis using assms by auto
  qed
next
  case (Cons x xs)
  from Cons have "a\<^sub>1 \<noteq> []" by auto
  then show ?thesis
    using assms prod_list_mat_closed[of "E\<^sub>I I" a\<^sub>1]
      submonoid_E\<^sub>I
      P\<^sub>I_closed_E\<^sub>I_mul_left[of "prod_list_mat a\<^sub>1" M]
    by auto
qed

lemma P\<^sub>I_closed_E\<^sub>I_prod_right:
  assumes "M \<in> P\<^sub>I I" "set a\<^sub>1 \<subseteq> E\<^sub>I I"
  shows "M * prod_list_mat a\<^sub>1 \<in> P\<^sub>I I"
  using assms(2)
proof (cases "a\<^sub>1")
  case Nil
  then have "prod_list_mat a\<^sub>1 = 1\<^sub>m n" by auto
  then have "M * prod_list_mat a\<^sub>1 = M" using P\<^sub>I_el_in_carr[of M] assms(1) by auto
  then show ?thesis using assms by auto
next
  case (Cons x xs)
  then have "a\<^sub>1 \<noteq> []" by auto
  then show ?thesis
    using assms prod_list_mat_closed[of "E\<^sub>I I" a\<^sub>1]
      submonoid_E\<^sub>I P\<^sub>I_closed_E\<^sub>I_mul_right[of "prod_list_mat a\<^sub>1" M]
    by auto
qed



lemma one_in_M\<^sub>I[simp]: "1\<^sub>m n \<in> M\<^sub>I I"
proof -
  {
    fix i
    assume i_p: "i \<in> I"
    then have "i < n" using I0 by auto
    then have "1\<^sub>m n $$ (i,i) \<ge> (1 :: 'a)" by auto
    then have "\<exists>j \<in> I. 1\<^sub>m n $$ (i,j) \<ge> (1 :: 'a)"
      using i_p 
      by auto
  }
  then show ?thesis unfolding M\<^sub>I_def using one_in_N by auto
qed

lemma L\<^sub>I_in_N: "L\<^sub>I I \<subseteq> N"
  using L\<^sub>I_def by auto

lemma M\<^sub>I_in_N: "M\<^sub>I I \<subseteq> N"
  using M\<^sub>I_def by auto

lemma M\<^sub>I_el_in_N:
  assumes "x \<in> M\<^sub>I I"
  shows "x \<in> N"
  using assms M\<^sub>I_in_N in_mono by auto

lemma L\<^sub>I_el_in_N:
  assumes "x \<in> L\<^sub>I I"
  shows "x \<in> N"
  using assms L\<^sub>I_in_N in_mono by auto

lemma M\<^sub>I_in_carr: "M\<^sub>I I \<subseteq> carrier_mat n n"
  using subset_trans[of "M\<^sub>I I" N] M\<^sub>I_in_N N_in_carr by auto

lemma M\<^sub>I_el_in_carr:
  assumes "x \<in> M\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms M\<^sub>I_in_carr in_mono by auto

lemma L\<^sub>I_el_in_carr:
  assumes "x \<in> L\<^sub>I I"
  shows "x \<in> carrier_mat n n"
  using assms L\<^sub>I_def N_def by auto

lemma M\<^sub>I_greater_zero:
  assumes "x \<in> M\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from assms[unfolded M\<^sub>I_def] I_non_empty obtain i j where "i \<in> I" "j \<in> I" "x $$ (i, j) \<ge> 1"
    by fastforce
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from \<open>j \<in> I\<close> I0 have "j < n" by auto
  moreover
  from assms M\<^sub>I_el_in_carr M\<^sub>I_el_in_N N_greater_eq_zero have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis using compat[OF _ one_gt_zero] by auto
qed

lemma L\<^sub>I_greater_zero:
  assumes "x \<in> L\<^sub>I I"
  shows "x >\<^sub>m 0\<^sub>m n n"
proof -
  from assms[unfolded L\<^sub>I_def] I_non_empty obtain i j where "i \<in> I" "j \<in> I" "x $$ (i, j) \<succ> 0"
    by fastforce
  moreover
  from \<open>i \<in> I\<close> I0 have "i < n" by auto
  moreover
  from \<open>j \<in> I\<close> I0 have "j < n" by auto
  moreover
  from assms L\<^sub>I_el_in_carr L\<^sub>I_el_in_N N_greater_eq_zero have "x \<ge>\<^sub>m 0\<^sub>m n n" by auto
  ultimately show ?thesis by auto
qed


lemma L\<^sub>I_in_P: "L\<^sub>I I \<subseteq> P"
  using L\<^sub>I_greater_zero L\<^sub>I_el_in_carr P_greater_zero by auto

lemma M\<^sub>I_in_P: "M\<^sub>I I \<subseteq> P"
  using M\<^sub>I_greater_zero M\<^sub>I_el_in_carr P_greater_zero by auto


lemma M\<^sub>I_closed_mult:
  assumes "A \<in> M\<^sub>I I" "B \<in> M\<^sub>I I"
  shows "A * B \<in> M\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>j \<in> I. (A * B) $$ (i,j) \<ge> 1"
  proof -
    fix i
    assume "i \<in> I"
    from \<open>i \<in> I\<close> obtain j1 where j1_p: "A $$ (i, j1) \<ge> 1" "j1 \<in> I"
      using assms(1)[unfolded M\<^sub>I_def]
      by auto
    from \<open>j1 \<in> I\<close> obtain j2 where j2_p: "B $$ (j1, j2) \<ge> 1" "j2 \<in> I"
      using assms(2)[unfolded M\<^sub>I_def]
      by auto
    have "i < n" using \<open>i \<in> I\<close> I0 by auto
    have "j1 < n" using \<open>j1 \<in> I\<close> I0 by auto
    have "j2 < n" using \<open>j2 \<in> I\<close> I0 by auto
    have id: "(A * B) $$ (i, j2) = (\<Sum> k \<in> {..< n}. A $$ (i,k) * B $$ (k,j2))"
      using M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>  assms mat_mult_compo_alt by blast
    have "A $$ (i, j1) * B $$ (j1, j2) \<ge> 1"
      using j1_p j2_p M\<^sub>I_el_in_carr assms
      by auto
    moreover
    have "\<And>k. k < n \<Longrightarrow> A $$ (i,k) * B $$ (k,j2) \<ge> 0"
      using assms M\<^sub>I_el_in_N M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j2]
            mult_nonneg_nonneg[of "A $$ (i,_)" "B $$ (_,j2)"]
      by auto
    ultimately have "(A * B) $$ (i, j2) \<ge> 1 + 0"
      unfolding id using \<open>j1 < n\<close>
      by (subst sum.remove[of _ j1], force, force, intro plus_mono sum_nonneg, auto)
    then show "\<exists>j \<in> I. (A * B) $$ (i, j) \<ge> 1"
      using \<open>j2 \<in> I\<close>
      by auto
  qed
  moreover
  have "A * B \<in> N"
    using N_mult_closed assms M\<^sub>I_el_in_N
    by auto
  ultimately
  show ?thesis unfolding M\<^sub>I_def by auto
qed

lemma M\<^sub>I_closed_L\<^sub>I_prod_left:
  assumes "A \<in> M\<^sub>I I" "B \<in> L\<^sub>I I"
  shows "A * B \<in> L\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>j \<in> I. (A * B) $$ (i,j) \<succ> 0"
  proof -
    fix i
    assume "i \<in> I"
    from \<open>i \<in> I\<close> obtain j1 where j1_p: "A $$ (i, j1) \<ge> 1" "j1 \<in> I"
      using assms(1)[unfolded M\<^sub>I_def]
      by auto
    from \<open>j1 \<in> I\<close> obtain j2 where j2_p: "B $$ (j1, j2) \<succ> 0" "j2 \<in> I"
      using assms(2)[unfolded L\<^sub>I_def]
      by auto
    have "i < n" using \<open>i \<in> I\<close> I0 by auto
    have "j1 < n" using \<open>j1 \<in> I\<close> I0 by auto
    have "j2 < n" using \<open>j2 \<in> I\<close> I0 by auto
    have id: "(A * B) $$ (i, j2) = (\<Sum> k \<in> {..< n}. A $$ (i,k) * B $$ (k,j2))"
      using L\<^sub>I_el_in_carr M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>  assms mat_mult_compo_alt by blast
    have "A $$ (i, j1) * B $$ (j1, j2) \<succ> 0"
      using j1_p j2_p M\<^sub>I_el_in_carr assms by (metis ge_1_mult_pos)
    moreover
    have "\<And>k. k < n \<Longrightarrow> A $$ (i,k) * B $$ (k,j2) \<ge> 0"
      using assms L\<^sub>I_el_in_N M\<^sub>I_el_in_N L\<^sub>I_el_in_carr M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j2]
            mult_nonneg_nonneg[of "A $$ (i,_)" "B $$ (_,j2)"]
      by auto
    ultimately have "(A * B) $$ (i, j2) \<succ> 0"
      unfolding id using \<open>j1 < n\<close>
      apply (subst sum.remove[of _ j1], force, force)
      by (metis (no_types, lifting) DiffE add_increasing2 lessThan_iff compat ge_refl
          sum_nonneg)
    then show "\<exists>j \<in> I. (A * B) $$ (i, j) \<succ> 0"
      using \<open>j2 \<in> I\<close>
      by auto
  qed
  moreover
  have "A * B \<in> N"
    using N_mult_closed assms L\<^sub>I_el_in_N M\<^sub>I_el_in_N
    by auto
  ultimately
  show ?thesis unfolding L\<^sub>I_def by auto
qed

lemma M\<^sub>I_closed_L\<^sub>I_prod_right:
  assumes "A \<in> L\<^sub>I I" "B \<in> M\<^sub>I I"
  shows "A * B \<in> L\<^sub>I I"
proof -
  have "\<And>i. i \<in> I \<Longrightarrow> \<exists>j \<in> I. (A * B) $$ (i,j) \<succ> 0"
  proof -
    fix i
    assume "i \<in> I"
    from \<open>i \<in> I\<close> obtain j1 where j1_p: "A $$ (i, j1) \<succ> 0" "j1 \<in> I"
      using assms(1)[unfolded L\<^sub>I_def]
      by auto
    from \<open>j1 \<in> I\<close> obtain j2 where j2_p: "B $$ (j1, j2) \<ge> 1" "j2 \<in> I"
      using assms(2)[unfolded M\<^sub>I_def]
      by auto
    have "i < n" using \<open>i \<in> I\<close> I0 by auto
    have "j1 < n" using \<open>j1 \<in> I\<close> I0 by auto
    have "j2 < n" using \<open>j2 \<in> I\<close> I0 by auto
    have id: "(A * B) $$ (i, j2) = (\<Sum> k \<in> {..< n}. A $$ (i,k) * B $$ (k,j2))"
      using L\<^sub>I_el_in_carr M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>  assms mat_mult_compo_alt by blast
    have "A $$ (i, j1) * B $$ (j1, j2) \<succ> 0"
      using j1_p j2_p M\<^sub>I_el_in_carr assms
      by (metis compat gt_imp_ge mult.right_neutral mult_left_mono)
    moreover
    have "\<And>k. k < n \<Longrightarrow> A $$ (i,k) * B $$ (k,j2) \<ge> 0"
      using assms L\<^sub>I_el_in_N M\<^sub>I_el_in_N L\<^sub>I_el_in_carr M\<^sub>I_el_in_carr \<open>i < n\<close> \<open>j2 < n\<close>
            N_compo_greater_eq_zero[of A i] N_compo_greater_eq_zero[of B _ j2]
            mult_nonneg_nonneg[of "A $$ (i,_)" "B $$ (_,j2)"]
      by auto
    ultimately have "(A * B) $$ (i, j2) \<succ> 0"
      unfolding id using \<open>j1 < n\<close>
      apply (subst sum.remove[of _ j1], force, force)
      by (metis (no_types, lifting) DiffE add_increasing2 lessThan_iff compat ge_refl
          sum_nonneg)
    then show "\<exists>j \<in> I. (A * B) $$ (i, j) \<succ> 0"
      using \<open>j2 \<in> I\<close>
      by auto
  qed
  moreover
  have "A * B \<in> N"
    using N_mult_closed assms L\<^sub>I_el_in_N M\<^sub>I_el_in_N
    by auto
  ultimately
  show ?thesis unfolding L\<^sub>I_def by auto
qed



lemma M\<^sub>I_closed_add:
  assumes "A \<in> M\<^sub>I I" "B \<in> N"
  shows "A + B \<in> M\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms M\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    fix i
    assume i_p: "i \<in> I"
    then obtain j where j_p: "j \<in> I" "A $$ (i,j) \<ge> 1"
      using assms[unfolded M\<^sub>I_def] by auto
    then have "i < n" "j < n" using i_p I0 by auto
    then have "B $$ (i,j) \<ge> 0"
      using assms(2) M\<^sub>I_el_in_N N_compo_greater_eq_zero2 by auto
    moreover
    have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> \<open>j < n\<close> by auto
    ultimately have "(A + B) $$ (i,j) \<ge> 1"
      using j_p(2) by (simp add: add_increasing2)
    then have "\<exists>j \<in> I. (A + B) $$ (i,j) \<ge> 1" using j_p(1) by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using M\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding M\<^sub>I_def by auto
qed

lemma L\<^sub>I_closed_add:
  assumes "A \<in> L\<^sub>I I" "B \<in> N"
  shows "A + B \<in> L\<^sub>I I"
proof -
  have Mcarr: "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" using assms L\<^sub>I_el_in_carr N_el_in_carr by auto
  {
    fix i
    assume i_p: "i \<in> I"
    then obtain j where j_p: "j \<in> I" "A $$ (i,j) \<succ> 0"
      using assms[unfolded L\<^sub>I_def] by auto
    then have "i < n" "j < n" using i_p I0 by auto
    then have "B $$ (i,j) \<ge> 0"
      using assms(2) M\<^sub>I_el_in_N N_compo_greater_eq_zero2 by auto
    moreover
    have "(A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
      using mat_add_compo_alt Mcarr \<open>i < n\<close> \<open>j < n\<close> by auto
    ultimately have "(A + B) $$ (i,j) \<succ> 0"
      using add_pos_nonneg[of "A $$ (i,j)" "B $$ (i,j)"] j_p(2)
      by (metis add_left_mono order_pair.compat order_pair_axioms verit_sum_simplify)
    then have "\<exists>j \<in> I. (A + B) $$ (i,j) \<succ> 0" using j_p(1) by auto
  }
  moreover
  have "A + B \<in> carrier_mat n n" using add_carrier_mat Mcarr by auto
  moreover
  have "A + B \<in> N"
    using L\<^sub>I_el_in_N N_add_closed assms by auto
  ultimately show ?thesis unfolding L\<^sub>I_def by auto
qed


lemma submonoid_M\<^sub>I: "submonoid (M\<^sub>I I) interp_mul_monoid_mat"
proof (unfold_locales, unfold interp_mul_monoid_mat_def, goal_cases)
  case 1
  then show ?case using M\<^sub>I_in_carr by simp
next
  case (2 x y)
  then show ?case using M\<^sub>I_closed_mult by simp
next
  case 3
  then show ?case using one_in_M\<^sub>I by simp
qed



subsection \<open>Main properties of the sets\<close>

theorem core_E\<^sub>I_is_P\<^sub>I: "P\<^sub>I I = core (E\<^sub>I I)"
proof
  show "P\<^sub>I I \<subseteq> core (E\<^sub>I I)"
  proof
    fix A
    assume asm1: "A \<in> P\<^sub>I I"
    show "A \<in> core (E\<^sub>I I)"
    proof -
      have "E\<^sub>I I \<subseteq> carrier_mat n n" using E\<^sub>I_in_carr by auto
      have res: "\<And>a\<^sub>1 a\<^sub>2. set a\<^sub>1 \<subseteq> E\<^sub>I I \<Longrightarrow> set a\<^sub>2 \<subseteq> E\<^sub>I I \<Longrightarrow>
                   (prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> P\<^sub>I I"
        by (simp add: P\<^sub>I_closed_E\<^sub>I_prod_left P\<^sub>I_closed_E\<^sub>I_prod_right asm1)
      from asm1 P\<^sub>I_el_in_carr[of A] have triv: "A \<in> carrier_mat n n" by auto
      from triv res core_def P\<^sub>I_in_P in_mono[of "P\<^sub>I I" P] show ?thesis
        by simp
    qed
  qed
  show "core (E\<^sub>I I) \<subseteq> P\<^sub>I I" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain A where Ac: "A \<in> core (E\<^sub>I I)" and API: "A \<notin> P\<^sub>I I" by auto
    from this[unfolded core_def, simplified]
    have A: "A \<in> carrier_mat n n" and inP: "set Bs \<subseteq> E\<^sub>I I \<Longrightarrow>
        prod_list_mat Bs * A * prod_list_mat Bs \<in> P" for Bs by auto 
    define B :: "'a mat" where "B = mat n n (\<lambda> (i,j). if i = j \<and> j \<in> I then 1 else 0)"
    have B_def_alt: "B = mat n n (\<lambda> (i,j). if i = j \<and> i \<in> I then 1 else 0)" 
      unfolding B_def by auto
    have BEI: "B \<in> E\<^sub>I I" and B: "B \<in> carrier_mat n n" unfolding E\<^sub>I_def N_def B_def using I0 one_ge_zero
      by (auto intro!: mat_geI)
    hence "set [B] \<subseteq> E\<^sub>I I" by auto
    from inP[OF this] A B 
    have BAB: "B * (A * B) \<in> P" by auto
    have [simp]: "vec n (\<lambda>i. 0) = 0\<^sub>v n" by (intro eq_vecI, auto) 
    have [simp]: "j < n \<Longrightarrow> vec n (\<lambda>i. if i = j then 1 else 0) = unit_vec n j" for j
      by auto
    have [simp]: "i < n \<Longrightarrow> vec n (\<lambda>j. if i = j then 1 else 0) = unit_vec n i" for i
      by auto
    define C where "C = mat n n (\<lambda> (i,j). if j \<in> I then A $$ (i,j) else 0)" 
    define D where "D = mat n n (\<lambda> (i,j). if i \<in> I \<and> j \<in> I then A $$ (i,j) else 0)" 
    have C: "C \<in> carrier_mat n n" unfolding C_def by auto
    have D: "D \<in> carrier_mat n n" unfolding D_def by auto
    have ABC: "A * B = C" unfolding C_def
      by (intro eq_matI, insert A B, auto simp: B_def)
    have BCD: "B * C = mat n n (\<lambda> (i,j). if i \<in> I then C $$ (i,j) else 0)"
      by (intro eq_matI, insert C B, auto simp: B_def_alt)
    have BAB_D: "B * (A * B) = D" 
      unfolding ABC BCD unfolding C_def D_def by auto
    from BAB[unfolded P_def BAB_D] 
    have "D >\<^sub>m 0\<^sub>m n n" by auto
    from mat_gtD[OF this] obtain i j
      where ij: "i < n" "j < n" and D0: "D $$ (i,j) \<succ> 0" by auto
    from D0[unfolded D_def] ij 
    have ij: "i \<in> I" "j \<in> I" and A0: "A $$ (i,j) \<succ> 0" by (auto split: if_splits)
    from core_in_P Ac have "A \<in> P" by auto
    hence "A \<in> N" using P_in_N by blast
    with API[unfolded P\<^sub>I_def] 
    have notA0: "\<And> i j. i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> \<not> A $$ (i,j) \<succ> 0" by auto
    with ij A0 show False by auto
  qed
qed

theorem core_M\<^sub>I_includes_L\<^sub>I: "L\<^sub>I I \<subseteq> core (M\<^sub>I I)"
proof
  fix A
  assume asm1: "A \<in> L\<^sub>I I"
  show "A \<in> core (M\<^sub>I I)"
  proof -
    {
      fix a\<^sub>1 a\<^sub>2
      assume a_p: "set a\<^sub>1 \<subseteq> M\<^sub>I I" "set a\<^sub>2 \<subseteq> M\<^sub>I I"
      have "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> L\<^sub>I I"
      proof -
        {
          fix K
          assume "K \<in> L\<^sub>I I"
          then have "K * prod_list_mat a\<^sub>2 \<in> L\<^sub>I I"
          proof (cases "a\<^sub>2 = []")
            case True
            from True have "prod_list_mat a\<^sub>2 = 1\<^sub>m n"
              using prod_list_mat.simps(1)
              by auto
            then have "K * prod_list_mat a\<^sub>2 = K"
              using right_mult_one_mat[of K] \<open>K \<in> L\<^sub>I I\<close> L\<^sub>I_el_in_carr[of K]
              by auto
            then show "K * prod_list_mat a\<^sub>2 \<in> L\<^sub>I I"
              using \<open>K \<in> L\<^sub>I I\<close>
              by auto
          next
            case False
            have "prod_list_mat a\<^sub>2 \<in> M\<^sub>I I"
              using prod_list_mat_closed[of "M\<^sub>I I" a\<^sub>2] submonoid_M\<^sub>I
                M\<^sub>I_in_carr a_p(2) \<open>a\<^sub>2 \<noteq> []\<close> M\<^sub>I_closed_mult
              by auto
            then show "K * prod_list_mat a\<^sub>2 \<in> L\<^sub>I I"
              using \<open>K \<in> L\<^sub>I I\<close> M\<^sub>I_closed_L\<^sub>I_prod_right
              by auto
          qed
        } note res1 = this
        show ?thesis proof (cases "a\<^sub>1 = []")
          case True
          hence "prod_list_mat a\<^sub>1 = 1\<^sub>m n"
            using prod_list_mat.simps(1)
            by auto
          then have "prod_list_mat a\<^sub>1 * A = A"
            using left_mult_one_mat[of A] asm1 L\<^sub>I_el_in_carr[of A]
            by auto
          then show "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> L\<^sub>I I"
            using asm1 res1
            by auto
        next
          case False
          have "prod_list_mat a\<^sub>1 \<in> M\<^sub>I I"
            using prod_list_mat_closed[of "M\<^sub>I I" a\<^sub>1] submonoid_M\<^sub>I
              False a_p(1) M\<^sub>I_in_carr M\<^sub>I_closed_mult
            by auto
          then have "prod_list_mat a\<^sub>1 * A \<in> L\<^sub>I I"
            using asm1 M\<^sub>I_closed_L\<^sub>I_prod_left
            by auto
          then show "(prod_list_mat a\<^sub>1 * A * prod_list_mat a\<^sub>2) \<in> L\<^sub>I I"
            using res1 by auto
        qed
      qed
    }
    then show ?thesis unfolding core_def
      using asm1 M\<^sub>I_el_in_carr L\<^sub>I_el_in_carr L\<^sub>I_in_P in_mono
      by auto
  qed
qed
end (*index set I non empty*)
end (*matrices of size n, type of carrier, and parameter gt *)

(* the other direction is core\<^sub>|\<^sub>I\<^sub>|\<^sub>*\<^sub>\<delta>(M\<^sub>I) \<subseteq> L\<^sub>I\<^sub>,\<^sub>\<delta>.  It requires different deltas for core and L. *)
lemma L\<^sub>I_includes_core_M\<^sub>I:
  fixes mono gt and 
  def :: "'a :: {ring_1,ordered_semiring_1,Rings.ordered_semiring_0,linorder,semiring_1,ordered_cancel_comm_monoid_add}"
assumes ring: "squared_ring_mat_with_assms mono def gt"
  and gt: "\<And> x y. gt x y = (x - y \<ge> of_nat (card I) * \<delta>)" 
  and I0: "I \<subseteq> {..<n}" "I \<noteq> {}" 
  and L: "L = squared_ring_mat.L\<^sub>I n (\<lambda> x y. x - y \<ge> \<delta>) I" 
  and M: "M = squared_ring_mat.M\<^sub>I n I" 
shows "squared_ring_mat_with_assms.core n gt M \<subseteq> L" 
proof (rule ccontr)
  interpret squared_ring_mat_with_assms mono n def gt by fact
  assume "\<not> ?thesis" 
  from this[unfolded  M]
  obtain A where Ac: "A \<in> core (M\<^sub>I I)" and ALI: "A \<notin> L" by auto
  from Ac[unfolded core_def, simplified]
  have A: "A \<in> carrier_mat n n" and inP: "set Bs \<subseteq> M\<^sub>I I \<Longrightarrow>
        prod_list_mat Bs * A * prod_list_mat Bs \<in> P" for Bs by auto 
  from core_in_P Ac have "A \<in> P" by auto
  hence "A \<in> N" using P_in_N by blast
  with ALI[unfolded L squared_ring_mat.L\<^sub>I_def] obtain k where kI: "k \<in> I" 
    and notA0: "\<And> j. j \<in> I \<Longrightarrow> \<not> A $$ (k,j) \<ge> \<delta>" by auto
  from kI I0 have k: "k < n" by auto

  define B :: "'a mat" where "B = mat n n (\<lambda> (i,j). if i \<in> I \<and> j = k then 1 else 0)"
  have BEI: "B \<in> M\<^sub>I I" and B: "B \<in> carrier_mat n n" 
    unfolding M\<^sub>I_def N_def B_def using I0 one_ge_zero k
    by (auto intro!: mat_geI bexI[OF _ kI])
  hence "set [B] \<subseteq> M\<^sub>I I" by auto
  from inP[OF this] A B 
  have BAB: "B * (A * B) \<in> P" by auto
  have [simp]: "vec n (\<lambda>i. 0) = 0\<^sub>v n" by (intro eq_vecI, auto) 
  have [simp]: "vec n (\<lambda>j. if j = k then 1 else 0) = unit_vec n k"
    using k by auto
  have [simp]: "i < n \<Longrightarrow> vec n (\<lambda>j. if i = j then 1 else 0) = unit_vec n i" for i
    by auto
  define S where "S i = sum (\<lambda> j. A $$ (i,j)) I" for i
  define C where "C = mat n n (\<lambda> (i,j). if j = k then S i else 0)" 
  define D where "D = mat n n (\<lambda> (i,j). if i \<in> I \<and> j = k then S k else 0)" 
  have C: "C \<in> carrier_mat n n" unfolding C_def by auto
  have D: "D \<in> carrier_mat n n" unfolding D_def by auto
  {
    fix i
    assume i: "i < n"
    have splitN: "{0..<n} = I \<union> ({..<n} - I)" using I0 by auto
    have "row A i \<bullet> vec n (\<lambda>j. if j \<in> I then 1 else 0) = S i" 
      unfolding S_def scalar_prod_def 
      apply simp
      apply (subst splitN)
      apply (subst sum.union_disjoint)
      subgoal using finite_subset[OF I0(1)] by auto
      subgoal by auto
      subgoal by auto
      subgoal using A i I0 by (auto simp: row_def intro!: sum.cong)
      done
  }
  hence ABC: "A * B = C" 
    unfolding C_def
    by (intro eq_matI, insert A B, auto simp: B_def)
  have BCD: "B * C = D" unfolding D_def C_def B_def using k
    by (intro eq_matI, auto)
  have BAB_D: "B * (A * B) = D" 
    unfolding ABC BCD unfolding C_def D_def by auto
  from BAB[unfolded P_def BAB_D] 
  have "D >\<^sub>m 0\<^sub>m n n" by auto
  from mat_gtD[OF this] obtain i j
    where ij: "i < n" "j < n" and D0: "gt (D $$ (i,j)) 0" by auto
  from D0[unfolded D_def] ij have "gt (S k) 0" by (auto split: if_splits)
  hence Sk\<delta>: "S k \<ge> of_nat (card I) * \<delta>" unfolding gt by auto
  from I0 have card: "card I \<noteq> 0"
    by (simp add: finite_subset)
  have "A $$ (k,j) < \<delta>" if "j \<in> I" for j using notA0[OF that, unfolded assms] 
    by auto
  from sum_bounded_above_strict[of I "(\<lambda> j. A $$ (k,j))" \<delta>, OF this,
      folded S_def] card
  have "S k < of_nat (card I) * \<delta>" by auto
  with Sk\<delta> show False by auto
qed


end