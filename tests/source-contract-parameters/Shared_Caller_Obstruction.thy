theory Shared_Caller_Obstruction
 imports "../../thys/Logic_Programming/LP_Prolog_Recursive_Entry"
begin

text \<open>A restricted ground replacement can destroy caller-output freeness
when that output shares with the helper input. This does not refute termination
or the conditional entry theorem; it refutes automatic continuation freeness.\<close>

definition caller_before :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" where
 "caller_before slot = (if slot=1 then LPIFun (LPCUser ''seed'') []
  else if slot=2 then LPIVar ''helper''
  else if slot=3 then lpp_argument_list []
  else LPIVar ''caller'')"

definition caller_binding :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" where
 "caller_binding v = (if v=''caller'' then
  LPIFun (LPCUser ''2:prolog_data_2f'') [LPIFun (LPCUser ''0:prolog_data_766172'') [],LPIFun (LPCUser ''seed'') []]
  else if v=''helper'' then LPIFun (LPCUser ''scalar'') [] else LPIVar v)"

definition caller_after where
 "caller_after slot = lp_isubst (caller_before slot) caller_binding"

lemma shared_caller_entry:
 "lpp_recursive_entry (Fun (LPCUser ''seed'') []) 0 1 2 3 4 caller_before"
proof -
 have tracked: "lpp_runtime_parameter (Fun (LPCUser ''seed'') []) (LPIFun (LPCUser ''seed'') [])"
  using lpp_runtime_parameter_initial[of "Fun (LPCUser ''seed'') []"] by simp
 show ?thesis using tracked lpp_argument_list_length[of "[]"]
  by (auto simp: lpp_recursive_entry_def caller_before_def)
qed

lemma shared_caller_replacement_allowed:
 "Fun (LPCUser ''2:prolog_data_2f'') [Fun (LPCUser ''0:prolog_data_766172'') [],Fun (LPCUser ''seed'') []]
  \<in> lpp_parameter_leaf_templates (LPCUser ''2:prolog_data_2f'') (LPCUser ''0:prolog_data_766172'') (Fun (LPCUser ''seed'') [])"
 by (simp add: lpp_parameter_leaf_templates_def)

lemma shared_caller_continuation_not_free:
 "lpc_free_knowledge {4} caller_before \<and> \<not>lpc_free_knowledge {4} caller_after"
 by (simp add: lpc_free_knowledge_def caller_before_def caller_after_def caller_binding_def)

lemma shared_caller_continuation_other_facts:
 "lpp_runtime_parameter (Fun (LPCUser ''seed'') []) (caller_after 2) \<and>
  lpp_list_length (caller_after 3) 0 \<and> lpp_finite_term (caller_after 4)"
proof -
 have tracked: "lpp_runtime_parameter (Fun (LPCUser ''seed'') []) (LPIFun (LPCUser ''scalar'') [])"
  unfolding lpp_runtime_parameter_def
  by (auto simp: lpp_parameter_return_def intro!: exI[of _ "Fun (LPCUser ''scalar'') []"])
 show ?thesis using tracked lpp_argument_list_length[of "[]"]
  by (simp add: caller_after_def caller_before_def caller_binding_def lpp_argument_list_subst)
qed

ML \<open>
val checked = @{thms shared_caller_entry shared_caller_replacement_allowed
 shared_caller_continuation_not_free shared_caller_continuation_other_facts};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted shared caller obstruction" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-shared-caller-obstruction/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Structural counterexample, not a formal source execution.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "SHARED_CALLER_OBSTRUCTION_KERNEL_CHECKED";
\<close>
end
