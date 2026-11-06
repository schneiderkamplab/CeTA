theory LP_Prolog_Partial_Integer_Body
  imports LP_Cut_Fresh_Head_Controls LP_Prolog_Integer_Recurrence_Body
begin

text \<open>Only observed integer arguments supply arithmetic facts. Unobserved
head arguments retain arbitrary actual values in the caller namespace. Fresh
body variables occupy the separate local namespace. Assignment targets may
not silently turn an unobserved head argument into a fresh result variable.\<close>

definition lpp_partial_environment where
  "lpp_partial_environment H K rho eta x =
    (if x\<in>set K then lpp_integer_value (rho x)
     else if x\<in>set H then lp_isubst (eta x) lpc_fresh_caller
     else lpc_fresh_local x)"

fun lpp_partial_recurrence_check where
  "lpp_partial_recurrence_check H K [] = True"
| "lpp_partial_recurrence_check H K (LPPRSet x e#ops) =
    (x\<notin>set H \<and> x\<notin>set K \<and> lpp_expression_check K e \<and>
      lpp_partial_recurrence_check H (x#K) ops)"
| "lpp_partial_recurrence_check H K (LPPRGuard f c reversed a b#ops) =
    (lpp_comparison_descriptor f c reversed \<and> lpp_expression_check K a \<and>
      lpp_expression_check K b \<and> lpp_partial_recurrence_check H K ops)"

lemma lpp_partial_expression_evaluation:
  assumes checked: "lpp_expression_check K e"
  shows "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) (lpp_partial_environment H K rho eta))
    (lpp_expression_value e rho)"
  by (rule lpp_expression_evaluation[OF checked]) (simp add: lpp_partial_environment_def)

lemma lpp_partial_environment_assignment:
  assumes head_fresh: "x\<notin>set H" and known_fresh: "x\<notin>set K"
  shows "lp_isubst (lpp_partial_environment H K rho eta y)
      (LPIVar(CHR ''1'' # x := lpp_integer_value n)) =
    lpp_partial_environment H (x#K) (rho(x:=n)) eta y"
  using head_fresh known_fresh
  by (auto simp: lpp_partial_environment_def lpp_integer_value_def
    lpc_fresh_local_assignment_preserves_caller lpc_fresh_local_assignment)

lemma lpp_partial_assignment_step:
  assumes head_fresh: "x\<notin>set H" and known_fresh: "x\<notin>set K"
    and checked: "lpp_expression_check K e"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_partial_environment H K rho eta)))
        (lpp_recurrence_goal (LPPRSet x e)#rest) @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_partial_environment H (x#K) (rho(x:=lpp_expression_value e rho)) eta))) rest @
        map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?env = "lpp_partial_environment H K rho eta"
  let ?n = "lpp_expression_value e rho"
  let ?mu = "LPIVar(CHR ''1'' # x := lpp_integer_value ?n)"
  have evaluated: "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) ?env) ?n"
    by (rule lpp_partial_expression_evaluation[OF checked])
  have assigned: "lpp_integer_unifier (?env x) ?n=Some ?mu"
    using head_fresh known_fresh by (simp add: lpp_partial_environment_def lpc_fresh_local_def)
  have binding: "(\<lambda>y. lp_isubst (?env y) ?mu)=
      lpp_partial_environment H (x#K) (rho(x:=?n)) eta"
    by (rule ext, rule lpp_partial_environment_assignment[OF head_fresh known_fresh])
  note step = lpp_integer_recurrence_assignment[OF evaluated assigned,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?env)) rest @
      map (lp_cut_map (\<lambda>t. lp_isubst t lpc_fresh_caller)) pending" and es=es and P=P]
  show ?thesis using step
    by (simp add: map_map lp_cut_map_comp lp_ieval_subst binding o_def
      lpc_fresh_local_assignment_preserves_caller)
qed

ML \<open>
val checked = [@{thm lpp_partial_assignment_step}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted partial arithmetic body dependency" else ();
\<close>
end
