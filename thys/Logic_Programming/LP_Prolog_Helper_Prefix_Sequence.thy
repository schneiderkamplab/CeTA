theory LP_Prolog_Helper_Prefix_Sequence
  imports LP_Prolog_Helper_Prefix_Steps
begin

lemma lpp_checked_helper_operation_steps:
  assumes checked: "lpp_check_helper_operation P H K op"
    and ctx: "lpp_caller_numeric_context H K rho eta names"
    and guards: "lpp_helper_operation_guards op rho"
  shows "\<exists>next_eta next_names next_pending bars.
    lpp_caller_numeric_context H (lpp_helper_operation_known K op)
      (lpp_helper_operation_values op rho) next_eta next_names \<and> lp_cut_barriers bars \<and>
    (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (lpp_helper_operation_goal op#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending)#(bars@saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
proof (cases op)
  case (LPPHPrimitive primitive)
  show ?thesis
  proof (cases primitive)
    case (LPPRSet x e)
    have local_fresh: "x\<notin>set H" and unknown: "x\<notin>set K" and expression: "lpp_expression_check K e"
      using checked by (simp_all add: LPPHPrimitive LPPRSet)
    let ?n = "lpp_expression_value e rho"
    let ?next = "\<lambda>y. lp_isubst (eta y) (LPIVar(names x:=lpp_integer_value ?n))"
    let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t (LPIVar(names x:=lpp_integer_value ?n)))) pending"
    note typed = lpp_caller_numeric_assignment[OF ctx local_fresh unknown, where n="?n"]
    note step = lpp_caller_assignment_step[OF ctx local_fresh unknown expression,
      where rest=rest and pending=pending and saved=saved and P=P]
    show ?thesis
      apply (rule exI[of _ "?next"], rule exI[of _ names], rule exI[of _ "?pending"], rule exI[of _ "[]"])
      using typed step by (auto simp: LPPHPrimitive LPPRSet intro: r_into_rtrancl)
  next
    case (LPPRGuard f c reversed a b)
    have descriptor: "lpp_comparison_descriptor f c reversed"
      and left: "lpp_expression_check K a" and right: "lpp_expression_check K b"
      and holds: "lpp_integer_compare c (lpp_expression_value (if reversed then b else a) rho)
        (lpp_expression_value (if reversed then a else b) rho)"
      using checked guards by (auto simp: LPPHPrimitive LPPRGuard)
    note step = lpp_caller_comparison_step[OF ctx descriptor left right holds,
      where rest=rest and pending=pending and saved=saved and P=P]
    show ?thesis
      apply (rule exI[of _ eta], rule exI[of _ names], rule exI[of _ pending], rule exI[of _ "[]"])
      using ctx step by (auto simp: LPPHPrimitive LPPRGuard intro: r_into_rtrancl)
  qed
next
  case (LPPHCall s)
  have site: "lpp_check_helper_site P H K s" and holds: "lpp_helper_site_guards s rho"
    using checked guards by (simp_all add: LPPHCall)
  let ?n = "lpp_helper_site_value s rho"
  let ?next = "lpp_helper_caller_environment eta (names (lpphs_output s)) ?n"
  let ?names = "\<lambda>y. CHR ''0''#names y"
  let ?pending = "map (lp_cut_map (\<lambda>t. lp_isubst t
    (lpc_fresh_caller(names (lpphs_output s):=lpp_integer_value ?n)))) pending"
  have typed: "lpp_caller_numeric_context H (lpphs_output s#K)
    (rho(lpphs_output s:=?n)) ?next ?names"
    and returned: "\<exists>mark. (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (lpp_helper_operation_goal (LPPHCall s)#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?next)) rest @ ?pending)#LPCBarrier mark#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+"
    using lpp_checked_helper_site_steps[OF site ctx holds, where rest=rest and pending=pending and saved=saved] by auto
  obtain mark where step: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (lpp_helper_operation_goal (LPPHCall s)#rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t ?next)) rest @ ?pending)#LPCBarrier mark#saved)
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>+" using returned by blast
  show ?thesis
    apply (rule exI[of _ "?next"], rule exI[of _ "?names"], rule exI[of _ "?pending"], rule exI[of _ "[LPCBarrier mark]"])
    using typed step by (auto simp: LPPHCall intro: trancl_into_rtrancl)
qed

fun lpp_helper_prefix_known where
  "lpp_helper_prefix_known K [] = K"
| "lpp_helper_prefix_known K (op#ops) = lpp_helper_prefix_known (lpp_helper_operation_known K op) ops"
fun lpp_helper_prefix_values where
  "lpp_helper_prefix_values [] rho = rho"
| "lpp_helper_prefix_values (op#ops) rho = lpp_helper_prefix_values ops (lpp_helper_operation_values op rho)"
fun lpp_helper_prefix_guards where
  "lpp_helper_prefix_guards [] rho = True"
| "lpp_helper_prefix_guards (op#ops) rho =
    (lpp_helper_operation_guards op rho \<and> lpp_helper_prefix_guards ops (lpp_helper_operation_values op rho))"
fun lpp_check_helper_prefix where
  "lpp_check_helper_prefix P H K [] = True"
| "lpp_check_helper_prefix P H K (op#ops) =
    (lpp_check_helper_operation P H K op \<and> lpp_check_helper_prefix P H (lpp_helper_operation_known K op) ops)"

lemma lpp_checked_helper_prefix_steps:
  assumes checked: "lpp_check_helper_prefix P H K ops"
    and ctx: "lpp_caller_numeric_context H K rho eta names"
    and guards: "lpp_helper_prefix_guards ops rho"
  shows "\<exists>next_eta next_names next_pending bars.
    lpp_caller_numeric_context H (lpp_helper_prefix_known K ops)
      (lpp_helper_prefix_values ops rho) next_eta next_names \<and> lp_cut_barriers bars \<and>
    (LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
        (map lpp_helper_operation_goal ops @ rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending)#(bars@saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
  using checked ctx guards
proof (induct ops arbitrary: K rho eta names pending saved)
  case Nil
  show ?case
    apply (rule exI[of _ eta], rule exI[of _ names], rule exI[of _ pending], rule exI[of _ "[]"])
    using Nil by simp
next
  case (Cons op ops)
  have check_op: "lpp_check_helper_operation P H K op"
    and check_tail: "lpp_check_helper_prefix P H (lpp_helper_operation_known K op) ops"
    and op_guards: "lpp_helper_operation_guards op rho"
    and tail_guards: "lpp_helper_prefix_guards ops (lpp_helper_operation_values op rho)"
    using Cons.prems by auto
  obtain mid_eta mid_names mid_pending bs where mid_ctx:
      "lpp_caller_numeric_context H (lpp_helper_operation_known K op) (lpp_helper_operation_values op rho) mid_eta mid_names"
    and bs: "lp_cut_barriers bs"
    and first: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta))
      (lpp_helper_operation_goal op#map lpp_helper_operation_goal ops @ rest) @ pending)#saved,
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t mid_eta)) (map lpp_helper_operation_goal ops @ rest) @ mid_pending)#(bs@saved))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using lpp_checked_helper_operation_steps[OF check_op Cons.prems(2) op_guards,
      where rest="map lpp_helper_operation_goal ops @ rest" and pending=pending and saved=saved] by blast
  obtain next_eta next_names next_pending cs where final_ctx:
      "lpp_caller_numeric_context H (lpp_helper_prefix_known (lpp_helper_operation_known K op) ops)
        (lpp_helper_prefix_values ops (lpp_helper_operation_values op rho)) next_eta next_names"
    and cs: "lp_cut_barriers cs"
    and last: "(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t mid_eta))
        (map lpp_helper_operation_goal ops @ rest) @ mid_pending)#(bs@saved),
      LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t next_eta)) rest @ next_pending)#(cs@(bs@saved)))
      \<in>(lpp_builtin_source P lpp_integer_source_builtin)\<^sup>*"
    using Cons.hyps[OF check_tail mid_ctx tail_guards, where pending=mid_pending and saved="bs@saved"] by blast
  show ?case
    apply (rule exI[of _ next_eta], rule exI[of _ next_names], rule exI[of _ next_pending], rule exI[of _ "cs@bs"])
    using final_ctx bs cs rtrancl_trans[OF first last] by (simp only: lpp_helper_prefix_known.simps lpp_helper_prefix_values.simps
      list.map append_Cons append_assoc list_all_append; blast)
qed

ML \<open>
val checked = [@{thm lpp_checked_helper_operation_steps}, @{thm lpp_checked_helper_prefix_steps}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted complete helper prefix composition" else ();
\<close>
end
