theory Code_Abstract_Char
  imports 
    Main
    "HOL-Library.Char_ord" 
begin

lemma digit0_ascii_of_iff [simp]:
  "digit0 (String.ascii_of c) \<longleftrightarrow> digit0 c"
  by (simp add: String.ascii_of_def)

lemma digit1_ascii_of_iff [simp]:
  "digit1 (String.ascii_of c) \<longleftrightarrow> digit1 c"
  by (simp add: String.ascii_of_def)

lemma digit2_ascii_of_iff [simp]:
  "digit2 (String.ascii_of c) \<longleftrightarrow> digit2 c"
  by (simp add: String.ascii_of_def)

lemma digit3_ascii_of_iff [simp]:
  "digit3 (String.ascii_of c) \<longleftrightarrow> digit3 c"
  by (simp add: String.ascii_of_def)

lemma digit4_ascii_of_iff [simp]:
  "digit4 (String.ascii_of c) \<longleftrightarrow> digit4 c"
  by (simp add: String.ascii_of_def)

lemma digit5_ascii_of_iff [simp]:
  "digit5 (String.ascii_of c) \<longleftrightarrow> digit5 c"
  by (simp add: String.ascii_of_def)

lemma digit6_ascii_of_iff [simp]:
  "digit6 (String.ascii_of c) \<longleftrightarrow> digit6 c"
  by (simp add: String.ascii_of_def)

lemma (in unique_euclidean_semiring_with_bit_operations) of_char_ascii_of:
  \<open>of_char (String.ascii_of c) = take_bit 7 (of_char c)\<close>
  by (simp add: of_char_def take_bit_horner_sum_bit_eq del: horner_sum_simps)
    simp

lemma (in unique_euclidean_semiring_with_bit_operations) ascii_of_char_of:
  \<open>String.ascii_of (char_of a) = char_of (take_bit 7 a)\<close>
  by (simp add: char_of_def bit_simps)

lemma (in comm_semiring_1) of_nat_of_char:
  \<open>of_nat (of_char c) = of_char c\<close>
  by (cases c) simp             

lemma (in comm_ring_1) of_int_of_char:
  \<open>of_int (of_char c) = of_char c\<close>
  by (cases c) simp

lemma integer_of_char_of_nat: "integer_of_char c = integer_of_nat (of_char c :: nat)" 
  apply (simp add: integer_of_char_def integer_of_nat_def)
  apply (simp add: of_nat_of_char)
  done

lemma (in semidom_divide) sum_list_dvdI: assumes "\<And> y. y \<in> set ys \<Longrightarrow> x dvd (y :: 'a)" 
  shows "x dvd sum_list ys" 
  using assms by (induct ys, auto)  

lemma size_char_eq_0 [code]:
  \<open>size c = 0\<close> for c :: char
  by (cases c) simp

lemma size'_char_eq_0 [code]:
  \<open>size_char c = 0\<close>
  by (cases c) simp

definition "char_integer = char_of_integer" 

lemma char_integer_of_char [code abstype]:
  \<open>char_integer (integer_of_char c) = c\<close>
  by (simp add: char_integer_def char_of_integer_def integer_of_char_def)

lemma [code]: "integer_of_char (char_of_integer x) = 
  (if 0 \<le> x \<and> x < 256 then x else x mod 256)" 
  unfolding char_of_integer_def integer_of_char_def
  by (simp add: unique_euclidean_semiring_numeral_class.mod_less)

lemma [code]:
  \<open>integer_of_char (Char b0 b1 b2 b3 b4 b5 b6 b7) = horner_sum of_bool 2 [b0, b1, b2, b3, b4, b5, b6, b7]\<close>
  by (simp add: integer_of_char_def)
                     
lemma [code]:
  \<open>digit0 c \<longleftrightarrow> bit (integer_of_char c) 0\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit1 c \<longleftrightarrow> bit (integer_of_char c) 1\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit2 c \<longleftrightarrow> bit (integer_of_char c) 2\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit3 c \<longleftrightarrow> bit (integer_of_char c) 3\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit4 c \<longleftrightarrow> bit (integer_of_char c) 4\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit5 c \<longleftrightarrow> bit (integer_of_char c) 5\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit6 c \<longleftrightarrow> bit (integer_of_char c) 6\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>digit7 c \<longleftrightarrow> bit (integer_of_char c) 7\<close>
  by (cases c) (simp add: integer_of_char_def)

lemma [code]:
  \<open>integer_of_char (char_of n) = (let s1 = if bit n 0 then 1 else 0;
          s2 = if bit n 1 then s1 + 2 else s1;
          s3 = if bit n 2 then s2 + 4 else s2;
          s4 = if bit n 3 then s3 + 8 else s3;
          s5 = if bit n 4 then s4 + 16 else s4;
          s6 = if bit n 5 then s5 + 32 else s5;
          s7 = if bit n 6 then s6 + 64 else s6;
          s8 = if bit n 7 then s7 + 128 else s7
       in s8)\<close>
  by (simp add: char_of_def integer_of_char_def)

lemma ascii_of_precode:
  \<open>integer_of_char (String.ascii_of c) = take_bit 7 (integer_of_char c)\<close>
  by (simp add: integer_of_char_def ascii_of_char_of of_char_ascii_of)

lemma [code]:
  \<open>integer_of_char (String.ascii_of c) = (let i = integer_of_char c
    in if i < 128 then i else i - 128)\<close>
proof -
  define i where "i = integer_of_char c" 
  have "0 \<le> i" "i < 256" unfolding i_def integer_of_char_def
    sorry
  thus ?thesis unfolding ascii_of_precode Let_def i_def[symmetric]
    sorry
qed

lemma [code]:
  \<open>HOL.equal c d \<longleftrightarrow> integer_of_char c = integer_of_char d\<close>
  by (simp add: integer_of_char_def equal)

lemma [code]:
  \<open>c \<le> d \<longleftrightarrow> integer_of_char c \<le> integer_of_char d\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof -
  have \<open>?P \<longleftrightarrow> of_nat (of_char c) \<le> (of_nat (of_char d) :: integer)\<close>
    by (simp add: less_eq_char_def)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: of_nat_of_char integer_of_char_def)
  finally show ?thesis .
qed

lemma [code]:
  \<open>c < d \<longleftrightarrow> integer_of_char c < integer_of_char d\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
proof -
  have \<open>?P \<longleftrightarrow> of_nat (of_char c) < (of_nat (of_char d) :: integer)\<close>
    by (simp add: less_char_def)
  also have \<open>\<dots> \<longleftrightarrow> ?Q\<close>
    by (simp add: of_nat_of_char integer_of_char_def)
  finally show ?thesis .
qed

lemma absdef_simps:
  \<open>horner_sum of_bool 2 [] = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (False # bs) = (0 :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (True # bs) = (1 :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (0 :: integer)\<close>
  \<open>horner_sum of_bool 2 (False # bs) = (numeral (Num.Bit0 n) :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (numeral n :: integer)\<close>
  \<open>horner_sum of_bool 2 (True # bs) = (numeral (Num.Bit1 n) :: integer) \<longleftrightarrow> horner_sum of_bool 2 bs = (numeral n :: integer)\<close>
      apply simp_all
   apply (metis dvd_div_mult even_numeral mult_2 mult_numeral_1 numeral_Bit0 numeral_Bit0_div_2)
  apply (metis add.commute dvd_triv_left even_succ_div_2 mult_2 nonzero_mult_div_cancel_left numeral_Bit1 zero_neq_numeral)
  done

local_setup \<open>
  let
    val simps = @{thms absdef_simps integer_of_char_def of_char_Char numeral_One}
    fun prove_eqn lthy n lhs def_eqn =
      let
        val eqn = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
          (\<^term>\<open>integer_of_char\<close> $ lhs, HOLogic.mk_number \<^typ>\<open>integer\<close> n)
      in
        Goal.prove_future lthy [] [] eqn (fn {context = ctxt, ...} =>
          unfold_tac ctxt (def_eqn :: simps))
      end
    fun define n =
      let
        val s = "Char_" ^ String_Syntax.hex n;
        val b = Binding.name s;
        val b_def = Thm.def_binding b;
        val b_code = Binding.name (s ^ "_code");
      in
        Local_Theory.define ((b, Mixfix.NoSyn),
          ((Binding.empty, []), HOLogic.mk_char n))
        #-> (fn (lhs, (_, raw_def_eqn)) =>
          Local_Theory.note ((b_def, @{attributes [code_abbrev]}), [HOLogic.mk_obj_eq raw_def_eqn])
          #-> (fn (_, [def_eqn]) => `(fn lthy => prove_eqn lthy n lhs def_eqn))
          #-> (fn raw_code_eqn => Local_Theory.note ((b_code, []), [raw_code_eqn]))
          #-> (fn (_, [code_eqn]) => Code.declare_abstract_eqn code_eqn))
      end
  in
    fold define (0 upto 255)
  end
\<close>

definition \<open>hello = ''Hello, world!''\<close>

definition \<open>dummy \<longleftrightarrow> CHR ''H'' < CHR ''J''\<close>

export_code hello dummy String.ascii_of String.explode char_of_integer integer_of_char
  in Haskell module_name BarD

end