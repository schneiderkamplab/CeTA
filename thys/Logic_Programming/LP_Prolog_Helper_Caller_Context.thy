theory LP_Prolog_Helper_Caller_Context
  imports LP_Prolog_Helper_Caller_Environment
begin

text \<open>The caller context tracks integer observations and distinct fresh
names for as-yet unused local variables. Unobserved head arguments remain
arbitrary actual terms. This is a proof invariant for the existing source
steps, not another execution relation.\<close>

definition lpp_caller_numeric_context where
  "lpp_caller_numeric_context H K rho eta names =
    (inj names \<and>
      (\<forall>y\<in>set K. eta y=lpp_integer_value (rho y)) \<and>
      (\<forall>y. y\<notin>set H \<longrightarrow> y\<notin>set K \<longrightarrow> eta y=LPIVar (names y)))"

lemma lpp_caller_numeric_initial:
  "lpp_caller_numeric_context H K rho (lpp_partial_environment H K rho eta) (\<lambda>y. CHR ''1''#y)"
  by (auto simp: lpp_caller_numeric_context_def lpp_partial_environment_def lpc_fresh_local_def inj_def)

lemma lpp_caller_numeric_assignment:
  assumes ctx: "lpp_caller_numeric_context H K rho eta names"
    and local_fresh: "x\<notin>set H" and unknown: "x\<notin>set K"
  shows "lpp_caller_numeric_context H (x#K) (rho(x:=n))
    (\<lambda>y. lp_isubst (eta y) (LPIVar(names x:=lpp_integer_value n))) names"
  using ctx local_fresh unknown
  by (auto simp: lpp_caller_numeric_context_def lpp_integer_value_def inj_eq)

lemma lpp_caller_numeric_helper:
  assumes ctx: "lpp_caller_numeric_context H K rho eta names"
    and local_fresh: "x\<notin>set H" and unknown: "x\<notin>set K"
  shows "lpp_caller_numeric_context H (x#K) (rho(x:=n))
    (lpp_helper_caller_environment eta (names x) n) (\<lambda>y. CHR ''0''#names y)"
  using ctx local_fresh unknown
  by (auto simp: lpp_caller_numeric_context_def lpp_helper_caller_environment_def
    lpc_fresh_caller_def lpp_integer_value_def inj_def)

ML \<open>
val checked = [@{thm lpp_caller_numeric_initial}, @{thm lpp_caller_numeric_assignment},
  @{thm lpp_caller_numeric_helper}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted caller context transport" else ();
\<close>
end
