theory LP_Prolog_Operation_Context
  imports LP_Prolog_Guarded_Returns LP_Prolog_Integer_Node_Domain
begin

text \<open>The typing evidence is interpreted at the operation's actual
pre-state environment. Final-path instances are insufficient: their later
substitutions cannot establish an earlier domain premise. The graph assembly
must provide successful helpers and guards already observed at this node.\<close>

definition lpp_check_operation_context where
  "lpp_check_operation_context T ps gs fs K =
    (lpp_check_path_types T ps gs fs \<and>
      list_all (\<lambda>x. x\<in>set (map lpp_transfer_variable fs)) K)"

lemma lpp_checked_operation_context:
  fixes P :: "'v lpp_success_clause list" and ps :: "'v lpp_success_atom list"
  assumes program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_check_operation_context T ps gs fs K"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and prefix: "list_all (lpp_guarded_success P lpp_integer_result)
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
  shows "lpp_integer_known K eta"
proof -
  have check: "lpp_check_path_types T ps gs fs"
    using checked by (simp add: lpp_check_operation_context_def)
  have known: "lpp_integer_known (map lpp_transfer_variable fs) eta"
    by (rule lpp_check_path_types_sound[where eta=eta and E=lpp_integer_result, OF program check guards prefix])
      (rule lpp_integer_result_contract)
  show ?thesis using known checked
    by (auto simp: lpp_check_operation_context_def lpp_integer_known_def list_all_iff)
qed

lemma lpp_checked_operation_is_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_operation_context T ps gs fs K"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and prefix: "list_all (lpp_guarded_success SP lpp_integer_result)
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    and node: "lpp_check_integer_is_node fuel P Q nds states nd ss K evidence a e rest active saved result_var k l next mode outputs yes no"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
  by (rule lpp_integer_is_node_domain[OF node])
    (rule lpp_checked_operation_context[OF program typing guards prefix])

lemma lpp_checked_operation_comparison_domain:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_operation_context T ps gs fs K"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and prefix: "list_all (lpp_guarded_success SP lpp_integer_result)
      (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    and node: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb rest active saved yes no"
  shows "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain
    (map fst (lpc_return_eval eta ss))"
  by (rule lpp_integer_comparison_node_domain[OF node])
    (rule lpp_checked_operation_context[OF program typing guards prefix])

ML \<open>
val checked = [@{thm lpp_checked_operation_context}, @{thm lpp_checked_operation_is_domain},
  @{thm lpp_checked_operation_comparison_domain}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted operation context dependency" else ();
\<close>
end
