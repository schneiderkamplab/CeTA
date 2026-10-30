theory LP_Prolog_Numeric_Code_Setup
 imports LP_Prolog_Numeric_Calls ITS_Ext.IA4_Instance
begin

derive ccompare ia4_sig ia4_variable
derive (eq) ceq ia4_sig ia4_variable
derive (rbt) set_impl ia4_sig ia4_variable
derive (rbt) mapping_impl ia4_variable
derive (no) cenum ia4_sig ia4_variable

lemma lpp_numeric_ground_code [code_unfold]:
  "(vars_term t = {}) = (vars_term_list t = [])"
  by (metis set_empty2 set_vars_term_list)

lemmas lpp_numeric_termination_code [code] =
  ia4_check_termination_def[unfolded lpp_numeric_ground_code]


text \<open>The component XML checker uses string variable names. Their carrier
is infinite, as is the carrier of tagged pre/post/intermediate variables.
Container complement operations therefore need no finite interval enumeration.\<close>

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

end
