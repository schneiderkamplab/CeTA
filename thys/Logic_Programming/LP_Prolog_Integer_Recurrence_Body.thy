theory LP_Prolog_Integer_Recurrence_Body
  imports LP_Prolog_Integer_Recurrence_Steps
begin

text \<open>Proof recipes for the existing source arithmetic steps. The recipe
must be matched to the original clause body; it supplies neither an alternative
operational semantics nor permission to skip a source goal.\<close>

datatype lpp_recurrence_operation =
    LPPRSet string "string lpp_integer_expression"
  | LPPRGuard string lpp_integer_comparison bool
      "string lpp_integer_expression" "string lpp_integer_expression"

fun lpp_recurrence_goal where
  "lpp_recurrence_goal (LPPRSet x e) = LPCAtom (Fun (LPCUser ''2:is'') [Var x,lpp_expression_term e])"
| "lpp_recurrence_goal (LPPRGuard f c reversed a b) =
    LPCAtom (Fun (LPCUser f) [lpp_expression_term a,lpp_expression_term b])"

fun lpp_recurrence_check where
  "lpp_recurrence_check K [] = True"
| "lpp_recurrence_check K (LPPRSet x e#ops) =
    (x\<notin>set K \<and> lpp_expression_check K e \<and> lpp_recurrence_check (x#K) ops)"
| "lpp_recurrence_check K (LPPRGuard f c reversed a b#ops) =
    (lpp_comparison_descriptor f c reversed \<and> lpp_expression_check K a \<and>
      lpp_expression_check K b \<and> lpp_recurrence_check K ops)"

fun lpp_recurrence_known where
  "lpp_recurrence_known K [] = K"
| "lpp_recurrence_known K (LPPRSet x e#ops) = lpp_recurrence_known (x#K) ops"
| "lpp_recurrence_known K (LPPRGuard f c reversed a b#ops) = lpp_recurrence_known K ops"

fun lpp_recurrence_values where
  "lpp_recurrence_values [] rho = rho"
| "lpp_recurrence_values (LPPRSet x e#ops) rho =
    lpp_recurrence_values ops (rho(x:=lpp_expression_value e rho))"
| "lpp_recurrence_values (LPPRGuard f c reversed a b#ops) rho = lpp_recurrence_values ops rho"

fun lpp_recurrence_guards where
  "lpp_recurrence_guards [] rho = True"
| "lpp_recurrence_guards (LPPRSet x e#ops) rho =
    lpp_recurrence_guards ops (rho(x:=lpp_expression_value e rho))"
| "lpp_recurrence_guards (LPPRGuard f c reversed a b#ops) rho =
    (lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho) \<and> lpp_recurrence_guards ops rho)"

definition lpp_recurrence_environment where
  "lpp_recurrence_environment K rho x = (if x\<in>set K then lpp_integer_value (rho x) else LPIVar x)"

lemma lpp_recurrence_environment_assignment:
  assumes fresh: "x\<notin>set K"
  shows "lp_isubst (lpp_recurrence_environment K rho y) (LPIVar(x:=lpp_integer_value n)) =
    lpp_recurrence_environment (x#K) (rho(x:=n)) y"
  using fresh by (auto simp: lpp_recurrence_environment_def)

lemma lpp_recurrence_expression_evaluation:
  assumes checked: "lpp_expression_check K e"
  shows "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) (lpp_recurrence_environment K rho))
    (lpp_expression_value e rho)"
  by (rule lpp_expression_evaluation[OF checked]) (simp add: lpp_recurrence_environment_def)

lemma lpp_recurrence_assignment_step:
  assumes fresh: "x\<notin>set K" and checked: "lpp_expression_check K e"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho)))
        (lpp_recurrence_goal (LPPRSet x e)#rest))#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_recurrence_environment (x#K) (rho(x:=lpp_expression_value e rho))))) rest)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?eta = "lpp_recurrence_environment K rho"
  let ?n = "lpp_expression_value e rho"
  let ?mu = "LPIVar(x:=lpp_integer_value ?n)"
  have evaluated: "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) ?eta) ?n"
    by (rule lpp_recurrence_expression_evaluation[OF checked])
  have assigned: "lpp_integer_unifier (?eta x) ?n=Some ?mu"
    using fresh by (simp add: lpp_recurrence_environment_def)
  note step = lpp_integer_recurrence_assignment[OF evaluated assigned,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) rest" and es=es and P=P]
  have environment: "(\<lambda>y. lp_isubst (?eta y) ?mu)=
    lpp_recurrence_environment (x#K) (rho(x:=?n))"
    by (rule ext, rule lpp_recurrence_environment_assignment[OF fresh])
  show ?thesis using step
    by (simp add: map_map lp_cut_map_comp lp_ieval_subst environment o_def)
qed


lemma lpp_recurrence_guard_step:
  assumes descriptor: "lpp_comparison_descriptor f c reversed"
    and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
    and holds: "lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
      (lpp_expression_value (if reversed then a else b) rho)"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho)))
        (lpp_recurrence_goal (LPPRGuard f c reversed a b)#rest))#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho))) rest)#es)
      \<in>lpp_builtin_source P lpp_integer_source_builtin"
proof -
  let ?eta = "lpp_recurrence_environment K rho"
  have guard: "lpp_integer_compare c (if reversed then lpp_expression_value b rho else lpp_expression_value a rho)
      (if reversed then lpp_expression_value a rho else lpp_expression_value b rho)"
    using holds by (cases reversed) auto
  note step = lpp_integer_recurrence_comparison_success[OF descriptor
    lpp_recurrence_expression_evaluation[OF left] lpp_recurrence_expression_evaluation[OF right] guard,
    where gs="map (lp_cut_map (\<lambda>t. lp_ieval t ?eta)) rest" and es=es and P=P]
  show ?thesis using step by simp
qed

lemma lpp_recurrence_body_source_steps:
  assumes checked: "lpp_recurrence_check K ops" and holds: "lpp_recurrence_guards ops rho"
  shows "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t (lpp_recurrence_environment K rho)))
        (map lpp_recurrence_goal ops @ rest))#es,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t
        (lpp_recurrence_environment (lpp_recurrence_known K ops) (lpp_recurrence_values ops rho)))) rest)#es)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
  using checked holds
proof (induct ops arbitrary: K rho)
  case Nil then show ?case by simp
next
  case (Cons op ops)
  show ?case
  proof (cases op)
    case (LPPRSet x e)
    have fresh: "x\<notin>set K" and expression: "lpp_expression_check K e"
      and tail_check: "lpp_recurrence_check (x#K) ops"
      and tail_guards: "lpp_recurrence_guards ops (rho(x:=lpp_expression_value e rho))"
      using Cons.prems by (auto simp: LPPRSet)
    note step = lpp_recurrence_assignment_step[OF fresh expression,
      where rest="map lpp_recurrence_goal ops @ rest" and es=es and P=P and rho=rho]
    note tail = Cons.hyps[OF tail_check tail_guards]
    show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] tail]
      by (simp only: LPPRSet list.map append_Cons lpp_recurrence_known.simps lpp_recurrence_values.simps)
  next
    case (LPPRGuard f c reversed a b)
    have descriptor: "lpp_comparison_descriptor f c reversed"
      and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
      and guard: "lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
        (lpp_expression_value (if reversed then a else b) rho)"
      and tail_check: "lpp_recurrence_check K ops" and tail_guards: "lpp_recurrence_guards ops rho"
      using Cons.prems by (auto simp: LPPRGuard)
    note step = lpp_recurrence_guard_step[OF descriptor left right guard,
      where rest="map lpp_recurrence_goal ops @ rest" and es=es and P=P]
    note tail = Cons.hyps[OF tail_check tail_guards]
    show ?thesis using rtrancl_trans[OF r_into_rtrancl[OF step] tail]
      by (simp only: LPPRGuard list.map append_Cons lpp_recurrence_known.simps lpp_recurrence_values.simps)
  qed
qed

ML \<open>
val checked = [@{thm lpp_recurrence_body_source_steps},
  @{thm lpp_integer_recurrence_first_clause_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted ordered recurrence body dependency" else ();
\<close>
end
