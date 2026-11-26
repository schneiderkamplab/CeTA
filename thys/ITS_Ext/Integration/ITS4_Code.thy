theory ITS4_Code
  imports ITS4_Parser
begin

text \<open>Instantiate the current container code setup for the extended
integer signature and quotient/remainder variables.\<close>
derive (eq) ceq ia4_sig ia4_variable
derive (compare) ccompare ia4_sig ia4_variable
derive (rbt) set_impl ia4_sig ia4_variable
derive (rbt) mapping_impl ia4_sig ia4_variable
derive (no) cenum ia4_sig ia4_variable

lemma its_ground_code [code_unfold]:
  "(vars_term t = {}) = (vars_term_list t = [])"
  by (metis set_empty2 set_vars_term_list)

lemmas its_termination_code [code] =
  ia4_check_termination_def[unfolded its_ground_code]

text \<open>String variables and their tagged transition variables have infinite
carriers; complement operations do not require finite enumeration.\<close>
instantiation trans_var :: ("{infinite,finite_UNIV}") card_UNIV
begin
definition "card_UNIV = Phantom('a trans_var) 0"
instance by (intro_classes) (simp add: card_UNIV_trans_var_def card_eq_0_iff finite_UNIV_trans_var infinite_UNIV)
end

instantiation trans_var :: ("{infinite,ccompare}") cproper_interval
begin
definition "cproper_interval = (\<lambda>(_ :: 'a trans_var option) _. False)"
instance by (intro_classes) (simp add: finite_UNIV_trans_var infinite_UNIV)
end

ML \<open>
val _ = if Thm_Deps.has_skip_proof [@{thm check_its4_sound}]
  then error "ITS soundness contains an admitted proof"
  else ();
\<close>

export_code check_its5_string check_its4_string Inl Inr char_of_integer integer_of_char in Haskell module_name ITS_Checker
end
