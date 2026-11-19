theory LP_Prolog_Observer_Internal_Coverage
 imports LP_Prolog_Observer_Internal_Assembly
begin

fun lpp_check_observer_equality_row where
 "lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i
  (Some (LPPFCut (LPCREquality a b gs active saved k l next mode outputs yes no) yes_facts no_facts)) (Some witness) =
  (states!i=(LPCGoals (LPCUnify a b#gs),active)#saved \<and>
   lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functors
    (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functors!i) yes no \<and>
   lpp_observer_equality_witness witness \<and>
   lpp_check_separation_action fuel P (nds!i) (contexts!i) (Fs!i) separation_contexts i (states!i)
    (LPPFCut (LPCREquality a b gs active saved k l next mode outputs yes no) yes_facts no_facts) witness)"
| "lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i row_action row_witness = False"

lemma lpp_checked_observer_equality_row:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i row_action row_witness"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
  (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 using checked
 by (cases "(T,fuel,P,Q,nds,states,contexts,Fs,functors,separation_contexts,i,row_action,row_witness)"
     rule: lpp_check_observer_equality_row.cases)
    (auto intro: lpp_observer_equality_receipt_sound[OF compatible transfer])

fun lpp_check_observer_univ_row where
 "lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i
  (Some (LPPFUniv value_var name_var args_var middle facts))
  (Some (LPPSUnivAction pair_symbol output_name output_args)) =
  (lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
    (nds!i) (Fs!i) (states!i) (contexts!i) (functors!i) returned arity
    (LPPFUniv value_var name_var args_var middle facts) \<and>
   lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args \<and>
   lpp_check_observer_univ_exit (Fs!i) (states!i))"
| "lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i row_action row_witness = False"

lemma lpp_checked_observer_univ_row:
 assumes checked: "lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i row_action row_witness"
 shows "\<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
  lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!i) (Fs!i) (states!i) (contexts!i) (functors!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts) \<and>
  lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and "lpp_check_observer_univ_exit (Fs!i) (states!i)"
proof -
 show "\<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
  lpp_check_functor_source_action T fuel P Q nds states contexts Fs functors
   (nds!i) (Fs!i) (states!i) (contexts!i) (functors!i) returned arity
   (LPPFUniv value_var name_var args_var middle facts) \<and>
  lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 using checked
 by (cases "(T,fuel,P,Q,nds,states,contexts,Fs,functors,separation_contexts,returned,arity,i,row_action,row_witness)"
     rule: lpp_check_observer_univ_row.cases; fastforce simp only: lpp_check_observer_univ_row.simps)
 show "lpp_check_observer_univ_exit (Fs!i) (states!i)"
 using checked
 by (cases "(T,fuel,P,Q,nds,states,contexts,Fs,functors,separation_contexts,returned,arity,i,row_action,row_witness)"
     rule: lpp_check_observer_univ_row.cases; fastforce simp only: lpp_check_observer_univ_row.simps)
qed

definition lpp_check_observer_internal_coverage where
 "lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses =
  (length states=length nds \<and> length contexts=length nds \<and> length Fs=length nds \<and>
   length functors=length nds \<and> length separation_contexts=length nds \<and>
   length actions=length nds \<and> length witnesses=length nds \<and>
   list_all (\<lambda>i.
    (lpp_observer_equality_frame (states!i) \<longrightarrow>
     lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i (actions!i) (witnesses!i)) \<and>
    (lpp_observer_may_univ (states!i) \<longrightarrow>
     lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i (actions!i) (witnesses!i))) [0..<length nds])"

lemma lpp_observer_internal_equality_coverage:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 and bound: "i<length nds"
 and shape: "lpp_observer_equality_frame (lpc_return_eval eta (states!i))"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functors
  (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
proof -
 have row: "lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i (actions!i) (witnesses!i)"
 using checked bound shape by (auto simp: lpp_check_observer_internal_coverage_def list_all_iff lpp_observer_equality_template)
 show ?thesis by (rule lpp_checked_observer_equality_row[OF compatible transfer row])
qed

lemma lpp_observer_internal_univ_coverage:
 assumes checked: "lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 and bound: "i<length nds"
 and shape: "lpp_observer_univ_frame (lpc_return_eval eta (states!i))"
 shows "lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i (actions!i) (witnesses!i)"
 using checked bound lpp_observer_univ_template[OF shape]
 by (auto simp: lpp_check_observer_internal_coverage_def list_all_iff)

ML \<open>
val thms = @{thms lpp_checked_observer_equality_row lpp_checked_observer_univ_row
 lpp_observer_internal_equality_coverage lpp_observer_internal_univ_coverage};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted internal observer table" else ();
\<close>
end
