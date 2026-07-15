theory Number_Parser
  imports 
    Show.Show_Instances
    Certification_Monads.Strict_Sum
    Certification_Monads.Parser_Monad
begin

context begin

text \<open>A natural number parser which is proven correct:\<close>

definition nat_of_digit :: "char \<Rightarrow> nat option" where
  "nat_of_digit x \<equiv>
    if x = CHR ''0'' then Some 0
    else if x = CHR ''1'' then Some 1
    else if x = CHR ''2'' then Some 2
    else if x = CHR ''3'' then Some 3
    else if x = CHR ''4'' then Some 4
    else if x = CHR ''5'' then Some 5
    else if x = CHR ''6'' then Some 6
    else if x = CHR ''7'' then Some 7
    else if x = CHR ''8'' then Some 8
    else if x = CHR ''9'' then Some 9
    else None"

private fun nat_of_string_aux :: "nat \<Rightarrow> string \<Rightarrow> nat option"
  where
    "nat_of_string_aux n [] = Some n" |
    "nat_of_string_aux n (d # s) = (nat_of_digit d \<bind> (\<lambda>m. nat_of_string_aux (10 * n + m) s))"

definition "nat_of_string s \<equiv>
  case if s = [] then None else nat_of_string_aux 0 s of
    None \<Rightarrow> Inl (STR ''cannot convert \"'' + String.implode s + STR ''\" to a number'')
  | Some n \<Rightarrow> Inr n"

private lemma nat_of_string_aux_snoc:
  "nat_of_string_aux n (s @ [c]) =
   do { l \<leftarrow> nat_of_string_aux n s; m \<leftarrow> nat_of_digit c; Some (10 * l + m) }"
  by (induct s arbitrary:n, auto)

private lemma nat_of_string_aux_digit:
  assumes m10: "m < 10"
  shows "nat_of_string_aux n (s @ string_of_digit m) =
    do { l \<leftarrow> nat_of_string_aux n s; Some (10 * l + m) }"
proof -
  from m10 have "m = 0 \<or> m = 1 \<or> m = 2 \<or> m = 3 \<or> m = 4 \<or> m = 5 \<or> m = 6 \<or> m = 7 \<or> m = 8 \<or> m = 9" 
    by presburger
  thus ?thesis by (auto simp add: nat_of_digit_def nat_of_string_aux_snoc string_of_digit.simps)
qed


private lemmas shows_move = showsp_nat_append[of 0 _ "[]",simplified, folded shows_prec_nat_def]

private lemma nat_of_string_aux_show: "nat_of_string_aux 0 (show m) = Some m"
proof (induct m rule:less_induct)
  case IH: (less m)
  show ?case proof (cases "m < 10")
    case m10: True
    show ?thesis
      apply (unfold shows_prec_nat_def)
      apply (subst showsp_nat.simps)
      using m10 nat_of_string_aux_digit[OF m10, of 0 "[]"]
      apply (auto simp add:shows_string_def nat_of_string_def string_of_digit.simps)
      done
  next
    case m: False
    then have "m div 10 < m" by auto
    note IH = IH[OF this]
    show ?thesis apply (unfold shows_prec_nat_def, subst showsp_nat.simps)
      using m apply (simp add: shows_prec_nat_def[symmetric] shows_string_def)
      apply (subst shows_move)
      using nat_of_string_aux_digit m IH 
      by (auto simp: nat_of_string_def)
  qed
qed

lemma fixes m :: nat shows show_nonemp: "show m \<noteq> []"
  apply (unfold shows_prec_nat_def)
  apply (subst showsp_nat.simps)
  apply (fold shows_prec_nat_def)
  apply (unfold o_def)
  apply (subst shows_move)
  apply (auto simp: shows_string_def string_of_digit.simps)
  done

text \<open>The parser \<open>nat_of_string\<close> is the inverse of \<open>show\<close>.\<close>
lemma nat_of_string_show[simp]: "nat_of_string (show m) = Inr m"
  using nat_of_string_aux_show by (auto simp: nat_of_string_def show_nonemp)

end


text \<open>We also provide a verified parser for integers.\<close>

fun safe_head where "safe_head [] = None" | "safe_head (x#xs) = Some x"

definition int_of_string :: "string \<Rightarrow> String.literal + int"
  where "int_of_string s \<equiv>
    if safe_head s = Some (CHR ''-'') then do 
       { n \<leftarrow> nat_of_string (tl s); Inr (- int n) }
    else do { n \<leftarrow> nat_of_string s; Inr (int n) }"

definition digit_chars where "digit_chars = 
  {CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'', CHR ''5'', CHR ''6'',
   CHR ''7'', CHR ''8'', CHR ''9'', CHR ''0''}" 

lemma range_string_of_digit: "set (string_of_digit x) \<subseteq> digit_chars" 
  unfolding digit_chars_def string_of_digit.simps by auto

lemma range_showsp_nat: "set (showsp_nat p n s) \<subseteq> digit_chars \<union> set s" 
proof (induct p n arbitrary: s rule: showsp_nat.induct)
  case (1 p n s)
  then show ?case using range_string_of_digit[of n] range_string_of_digit[of "n mod 10"]
    by (auto simp: showsp_nat.simps[of p n] shows_string_def) fastforce
qed

lemma range_show_nat: "set (show (n :: nat)) \<subseteq> digit_chars" 
  using range_showsp_nat[of 0 n Nil] unfolding shows_prec_nat_def by auto

lemma int_of_string_show[simp]: "int_of_string (show x) = Inr x" 
proof -
  have "show x = showsp_int 0 x []" 
    by (simp add: shows_prec_int_def)
  also have "\<dots> = (if x < 0 then ''-'' @ show (nat (-x)) else show (nat x))" 
    unfolding showsp_int_def if_distrib shows_prec_nat_def
    by (simp add: shows_string_def)
  also have "int_of_string \<dots> = Inr x" 
  proof (cases "x < 0")
    case True
    thus ?thesis unfolding int_of_string_def by simp
  next
    case False
    from range_show_nat have "set (show (nat x)) \<subseteq> digit_chars" .
    hence "CHR ''-'' \<notin> set (show (nat x))" unfolding digit_chars_def by auto
    hence "safe_head (show (nat x)) \<noteq> Some CHR ''-''" 
      by (cases "show (nat x)", auto) 
    thus ?thesis using False
      by (simp add: int_of_string_def)
  qed
  finally show ?thesis .
qed

end