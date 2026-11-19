theory LP_Prolog_Parameter_Sharing_Control
 imports LP_Prolog_Parameter_Leaf_Budget
begin

text \<open>A ground parameter can unify with a compound output. A variable
inside that output then receives a proper subterm of the parameter. The narrow
parameter replacement family is therefore not a contract for every variable
in a caller environment. A source proof must justify its observed coordinates.
This control does not refute the contract restricted to the traversed input.\<close>

lemma lpp_parameter_templates_not_subterm_closed:
 "(Fun (3::nat) [Fun 4 []] :: (nat,unit) term) \<notin>
   lpp_parameter_leaf_templates 0 1 (Fun 2 [Fun 3 [Fun 4 []]])"
 by (auto simp: lpp_parameter_leaf_templates_def)

lemma lpp_parameter_output_sharing_control:
 defines "c \<equiv> (Fun (2::nat) [Fun 3 [Fun 4 []]] :: (nat,unit) term)"
 defines "sigma \<equiv> (\<lambda>_::unit. Fun (3::nat) [Fun 4 []] :: (nat,unit) term)"
 shows "vars_term c = {} \<and> (Fun 2 [Var ()]) \<cdot> sigma = c \<and>
   sigma () \<notin> lpp_parameter_leaf_templates 0 1 c"
 by (auto simp: c_def sigma_def lpp_parameter_leaf_templates_def)

ML \<open>
val checked = @{thms lpp_parameter_templates_not_subterm_closed
 lpp_parameter_output_sharing_control};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter sharing control" else ();
\<close>
end
