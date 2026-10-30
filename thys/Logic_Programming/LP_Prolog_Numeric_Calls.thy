theory LP_Prolog_Numeric_Calls
 imports LP_Prolog_Observed_Calls LP_Prolog_Numeric_Valuation
begin

text \<open>The numeric projection retains every argument at an arithmetic
call boundary. Auxiliary ITS coordinates are deliberately unconstrained by
this representation, and are chosen by the checked path witness.\<close>

definition lpp_numeric_tuple where
  "lpp_numeric_tuple names ts rho =
    (length names=length ts \<and>
      (\<forall>i<length names. ts!i=lpp_integer_value (rho (names!i))))"

lemma lpp_numeric_tuple_Nil[simp]: "lpp_numeric_tuple [] [] rho"
  by (simp add: lpp_numeric_tuple_def)

lemma lpp_numeric_tuple_Cons:
  "lpp_numeric_tuple (x#xs) (t#ts) rho =
    (t=lpp_integer_value (rho x) \<and> lpp_numeric_tuple xs ts rho)"
  by (auto simp: lpp_numeric_tuple_def less_Suc_eq_0_disj)

lemma lpp_numeric_tuple_exists:
  assumes names: "distinct names" and len: "length names=length ts"
    and typed: "list_all lpp_is_integer ts"
  shows "\<exists>rho. lpp_numeric_tuple names ts rho"
  using names len typed
proof (induct names arbitrary: ts)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain t us where ts: "ts=t#us" using Cons.prems by (cases ts) auto
  obtain n where t: "t=lpp_integer_value n"
    using Cons.prems ts by (auto simp: lpp_is_integer_def)
  obtain rho where child: "lpp_numeric_tuple xs us rho"
    using Cons.hyps Cons.prems ts by auto
  have "lpp_numeric_tuple xs us (rho(x:=n))"
    using child Cons.prems by (auto simp: lpp_numeric_tuple_def)
  then have "lpp_numeric_tuple (x#xs) ts (rho(x:=n))"
    by (simp add: ts t lpp_numeric_tuple_Cons)
  then show ?case by blast
qed

lemma lpp_numeric_tuple_subst:
  "lpp_numeric_tuple names ts rho \<Longrightarrow>
    lpp_numeric_tuple names (map (\<lambda>t. lp_isubst t sigma) ts) rho"
  by (auto simp: lpp_numeric_tuple_def)

lemma lpp_numeric_tuple_coordinates:
  assumes tuple: "lpp_numeric_tuple names ts rho"
    and equal: "\<And>x. x\<in>set names \<Longrightarrow> rho' x=rho x"
  shows "lpp_numeric_tuple names ts rho'"
  using tuple equal by (auto simp: lpp_numeric_tuple_def)

definition lpp_numeric_call where
  "lpp_numeric_call coordinates a rho =
    lpp_numeric_tuple (coordinates (fst a)) (snd a) rho"

lemma lpp_numeric_call_match:
  assumes matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and represented: "lpp_numeric_call coordinates a pre"
  shows "lpp_numeric_call coordinates (lpp_success_atom_eval h eta) pre"
  using lpp_numeric_tuple_subst[OF represented[unfolded lpp_numeric_call_def], of sigma]
    matching unfolding lpp_numeric_call_def lpp_success_iatom_subst_def
    by (metis fst_conv snd_conv)

lemma lpp_numeric_endpoint_tuple:
  assumes endpoints: "list_all (lpp_check_numeric_endpoint K) endpoints"
    and known: "lpp_integer_known K eta"
  shows "list_all lpp_is_integer (map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints)"
proof -
  obtain rho where typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
    using lpp_integer_known_environment[OF known] by blast
  have "lpp_is_integer (lp_ieval (fst (snd e)) eta)" if "e\<in>set endpoints" for e
  proof -
    obtain coordinate t expression where e: "e=(coordinate,t,expression)" by (cases e) auto
    have check: "lpp_check_numeric_endpoint K (coordinate,t,expression)"
      using endpoints that by (auto simp: list_all_iff e)
    show ?thesis using lpp_checked_numeric_endpoint[OF check typed]
      by (auto simp: e lpp_is_integer_def)
  qed
  then show ?thesis by (simp add: list_all_iff)
qed

lemma lpp_numeric_tuple_endpoint:
  assumes represented: "lpp_numeric_tuple (map fst endpoints)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) endpoints) rho"
    and member: "(coordinate,t,expression)\<in>set endpoints"
  shows "lp_ieval t eta=lpp_integer_value (rho coordinate)"
proof -
  obtain i where bound: "i<length endpoints" and row: "endpoints!i=(coordinate,t,expression)"
    using member by (auto simp: in_set_conv_nth)
  show ?thesis using represented bound row by (auto simp: lpp_numeric_tuple_def)
qed


record 'v lpp_numeric_call_receipt =
  lppnc_facts :: "'v lpp_transfer_fact list"
  lppnc_inputs :: "'v lpp_numeric_endpoint list"
  lppnc_outputs :: "'v lpp_numeric_endpoint list"
  lppnc_tests :: "'v lpp_numeric_condition list"
  lppnc_bindings :: "('v * string trans_var) list"
  lppnc_formula :: "string trans_var ia4_exp Formula.formula"

fun lpp_numeric_constraint_observation where
  "lpp_numeric_constraint_observation (LPPOInteger _) = False"
| "lpp_numeric_constraint_observation _ = True"

definition lpp_check_numeric_call_row where
  "lpp_check_numeric_call_row T coordinates locations system (triple::'v lpp_observed_triple) (receipt::'v lpp_numeric_call_receipt) =
    (case triple of ((h,ps,b,gs),os) \<Rightarrow>
      let K=map lpp_transfer_variable (lppnc_facts receipt);
          inputs=lppnc_inputs receipt; outputs=lppnc_outputs receipt;
          bindings=lppnc_bindings receipt; formula=lppnc_formula receipt
      in lpp_check_path_types T ps gs (lppnc_facts receipt) \<and>
        lpp_check_numeric_path K inputs outputs
          (filter lpp_numeric_constraint_observation os) (lppnc_tests receipt) bindings formula \<and>
        lpp_check_numeric_bindings inputs outputs bindings \<and>
        list_all (\<lambda>(x,v). x\<in>set K) bindings \<and>
        map fst inputs=coordinates (fst h) \<and>
        map (fst o snd) inputs=snd h \<and>
        map fst outputs=coordinates (fst b) \<and>
        map (fst o snd) outputs=snd b \<and>
        Transition (locations (fst h)) (locations (fst b)) formula\<in>transition_rules system \<and>
        assertion system (locations (fst h))=Conjunction [] \<and>
        assertion system (locations (fst b))=Conjunction [])"

lemma lpp_numeric_call_row_types:
  fixes P :: "'v lpp_success_clause list" and receipt :: "'v lpp_numeric_call_receipt"
  assumes checked: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    and transfer: "lpp_check_transfer_program T P receipts"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and facts: "list_all (lpp_guarded_success P lpp_integer_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
  shows "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
  by (rule lpp_check_path_types_sound[OF transfer _ guards facts lpp_integer_result_contract])
    (use checked in \<open>auto simp: lpp_check_numeric_call_row_def Let_def\<close>)

lemma lpp_numeric_call_row_output:
  assumes checked: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
  shows "\<exists>rho. lpp_numeric_call coordinates (lpp_success_atom_eval b eta) rho"
proof -
  let ?outputs = "lppnc_outputs receipt"
  have endpoints: "list_all (lpp_check_numeric_endpoint (map lpp_transfer_variable (lppnc_facts receipt))) ?outputs"
    and distinct: "distinct (map fst ?outputs)"
    and names: "map fst ?outputs=coordinates (fst b)"
    and terms: "map (fst o snd) ?outputs=snd b"
    using checked by (auto simp: lpp_check_numeric_call_row_def lpp_check_numeric_path_def Let_def)
  have typed: "list_all lpp_is_integer (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?outputs)"
    by (rule lpp_numeric_endpoint_tuple[OF endpoints known])
  obtain rho where tuple: "lpp_numeric_tuple (map fst ?outputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?outputs) rho"
    using lpp_numeric_tuple_exists[OF distinct _ typed] by auto
  have "lpp_numeric_call coordinates (lpp_success_atom_eval b eta) rho"
    using tuple names terms by (simp add: lpp_numeric_call_def lpp_success_atom_eval_def map_map o_def terms[symmetric])
  then show ?thesis by blast
qed

theorem lpp_checked_numeric_call_step:
  assumes checked: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    and known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    and observations: "list_all (lpp_numeric_observation_holds eta) os"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and represented: "lpp_numeric_call coordinates a pre"
  shows "\<exists>post. (State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system \<and>
    lpp_numeric_call coordinates (lpp_success_atom_eval b eta) post"
proof -
  let ?K = "map lpp_transfer_variable (lppnc_facts receipt)"
  let ?inputs = "lppnc_inputs receipt"
  let ?outputs = "lppnc_outputs receipt"
  let ?bindings = "lppnc_bindings receipt"
  let ?formula = "lppnc_formula receipt"
  have path: "lpp_check_numeric_path ?K ?inputs ?outputs
      (filter lpp_numeric_constraint_observation os) (lppnc_tests receipt) ?bindings ?formula"
    and admissible: "lpp_check_numeric_bindings ?inputs ?outputs ?bindings"
    and bound_types: "\<And>x v. (x,v)\<in>set ?bindings \<Longrightarrow> x\<in>set ?K"
    and input_names: "map fst ?inputs=coordinates (fst h)"
    and input_terms: "map (fst o snd) ?inputs=snd h"
    and output_names: "map fst ?outputs=coordinates (fst b)"
    and output_terms: "map (fst o snd) ?outputs=snd b"
    and member: "Transition (locations (fst h)) (locations (fst b)) ?formula\<in>transition_rules system"
    and initial_assertion: "assertion system (locations (fst h))=Conjunction []"
    and final_assertion: "assertion system (locations (fst b))=Conjunction []"
    using checked by (auto simp: lpp_check_numeric_call_row_def Let_def list_all_iff)
  have obs: "list_all (lpp_numeric_observation_holds eta) (filter lpp_numeric_constraint_observation os)"
    using observations by (auto simp: list_all_iff)
  have input_rep: "lpp_numeric_call coordinates (lpp_success_atom_eval h eta) pre"
    by (rule lpp_numeric_call_match[OF matching represented])
  have input_tuple: "lpp_numeric_tuple (map fst ?inputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?inputs) pre"
    using input_rep input_names input_terms
    by (simp add: lpp_numeric_call_def lpp_success_atom_eval_def map_map o_def input_terms[symmetric])
  obtain output_values where output_rep:
    "lpp_numeric_call coordinates (lpp_success_atom_eval b eta) output_values"
    using lpp_numeric_call_row_output[OF checked known] by blast
  have output_tuple: "lpp_numeric_tuple (map fst ?outputs)
      (map (\<lambda>e. lp_ieval (fst (snd e)) eta) ?outputs) output_values"
    using output_rep output_names output_terms
    by (simp add: lpp_numeric_call_def lpp_success_atom_eval_def map_map o_def output_terms[symmetric])
  have inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set ?inputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (pre coordinate)"
    by (rule lpp_numeric_tuple_endpoint[OF input_tuple])
  have outputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set ?outputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (output_values coordinate)"
    by (rule lpp_numeric_tuple_endpoint[OF output_tuple])
  have before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system (locations (fst h)))"
    by (simp add: initial_assertion)
  have after: "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system (locations (fst b)))"
    by (simp add: final_assertion)
  have witness: "\<exists>post. (State (lpp_integer_assignment pre) (locations (fst h)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system \<and>
      (\<forall>coordinate\<in>set (map fst ?outputs). post coordinate = output_values coordinate)"
  proof (rule lpp_checked_numeric_path_witness[where eta=eta and pre=pre and output_values=output_values,
      OF path admissible obs known])
    fix x v assume "(x,v)\<in>set ?bindings"
    then show "x\<in>set ?K" by (rule bound_types)
  next
    fix coordinate t e assume member: "(coordinate,t,e)\<in>set ?inputs"
    show "lp_ieval t eta=lpp_integer_value (pre coordinate)" by (rule inputs[OF member])
  next
    fix coordinate t e assume member: "(coordinate,t,e)\<in>set ?outputs"
    show "lp_ieval t eta=lpp_integer_value (output_values coordinate)" by (rule outputs[OF member])
  next
    show "Transition (locations (fst h)) (locations (fst b)) ?formula\<in>transition_rules system" by (rule member)
    show "IA4.satisfies (lpp_integer_assignment pre) (assertion system (locations (fst h)))" by (rule before)
    show "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system (locations (fst b)))" by (rule after)
  qed
  obtain post where step: "(State (lpp_integer_assignment pre) (locations (fst h)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system"
    and coordinates: "\<forall>coordinate\<in>set (map fst ?outputs). post coordinate = output_values coordinate"
    using witness by blast
  have post: "lpp_numeric_call coordinates (lpp_success_atom_eval b eta) post"
    unfolding lpp_numeric_call_def
    by (rule lpp_numeric_tuple_coordinates[OF output_rep[unfolded lpp_numeric_call_def]])
      (use coordinates output_names in \<open>auto simp: lpp_success_atom_eval_def\<close>)
  have predicate: "fst a=fst h"
    using arg_cong[OF matching, of fst]
    by (simp add: lpp_success_iatom_subst_def lpp_success_atom_eval_def)
  show ?thesis using step post predicate by auto
qed


definition lpp_check_numeric_calls where
  "lpp_check_numeric_calls T coordinates locations system D row_receipts =
    (length D=length row_receipts \<and>
      list_all (\<lambda>i. lpp_check_numeric_call_row T coordinates locations system (D!i) (row_receipts!i)) [0..<length D])"

lemma lpp_numeric_calls_row:
  assumes checked: "lpp_check_numeric_calls T coordinates locations system D row_receipts"
    and member: "triple\<in>set D"
  shows "\<exists>receipt. lpp_check_numeric_call_row T coordinates locations system triple receipt"
proof -
  obtain i where bound: "i<length D" and triple: "D!i=triple"
    using member by (auto simp: in_set_conv_nth)
  have "lpp_check_numeric_call_row T coordinates locations system triple (row_receipts!i)"
    using checked bound triple by (auto simp: lpp_check_numeric_calls_def list_all_iff)
  then show ?thesis by blast
qed

theorem lpp_checked_numeric_calls_SN:
  fixes P :: "'v lpp_success_clause list" and row_receipts :: "'v lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_numeric_calls T coordinates locations system D row_receipts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and child: "SN (LPPIntegerLTS.transition system)"
  shows "SN (lpp_observed_calls (set D) P)"
proof (rule lpp_typed_relational_simulation_SN[where
    T="\<lambda>a. \<exists>pre. lpp_numeric_call coordinates a pre" and
    rep="\<lambda>a s. \<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre" and S="LPPIntegerLTS.transition system"])
  fix a target assume step: "(a,target)\<in>lpp_observed_calls (set D) P"
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and observations: "list_all (lpp_numeric_observation_holds eta) os"
    and facts: "list_all (lpp_guarded_success P lpp_integer_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_observed_calls_def)
  obtain receipt where row: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    using lpp_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    by (rule lpp_numeric_call_row_types[OF row transfer guards facts])
  show "\<exists>pre. lpp_numeric_call coordinates target pre"
    using lpp_numeric_call_row_output[OF row known] target by simp
next
  fix a assume typed: "\<exists>pre. lpp_numeric_call coordinates a pre"
  obtain pre where represented: "lpp_numeric_call coordinates a pre" using typed by blast
  have sn: "SN_on (LPPIntegerLTS.transition system)
    {State (lpp_integer_assignment pre) (locations (fst a))}"
    by (rule SN_on_subset2[OF subset_UNIV child])
  show "\<exists>s. (\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre) \<and> SN_on (LPPIntegerLTS.transition system) {s}"
    using represented sn by blast
next
  fix a target s
  assume step: "(a,target)\<in>lpp_observed_calls (set D) P"
    and typed: "\<exists>pre. lpp_numeric_call coordinates a pre"
    and represented: "\<exists>pre. s=State (lpp_integer_assignment pre) (locations (fst a)) \<and>
      lpp_numeric_call coordinates a pre"
  obtain pre where s: "s=State (lpp_integer_assignment pre) (locations (fst a))"
    and pre: "lpp_numeric_call coordinates a pre" using represented by blast
  obtain h ps b gs os sigma eta where member: "((h,ps,b,gs),os)\<in>set D"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) gs"
    and observations: "list_all (lpp_numeric_observation_holds eta) os"
    and facts: "list_all (lpp_guarded_success P lpp_integer_result) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    and target: "target=lpp_success_atom_eval b eta"
    using step by (auto simp: lpp_observed_calls_def)
  obtain receipt where row: "lpp_check_numeric_call_row T coordinates locations system ((h,ps,b,gs),os) receipt"
    using lpp_numeric_calls_row[OF checked member] by blast
  have known: "lpp_integer_known (map lpp_transfer_variable (lppnc_facts receipt)) eta"
    by (rule lpp_numeric_call_row_types[OF row transfer guards facts])
  obtain post where edge: "(State (lpp_integer_assignment pre) (locations (fst a)),
      State (lpp_integer_assignment post) (locations (fst b)))\<in>LPPIntegerLTS.transition system"
    and post: "lpp_numeric_call coordinates (lpp_success_atom_eval b eta) post"
    using lpp_checked_numeric_call_step[OF row known observations matching pre] by blast
  show "\<exists>t. (s,t)\<in>LPPIntegerLTS.transition system \<and>
    (\<exists>pre. t=State (lpp_integer_assignment pre) (locations (fst target)) \<and>
      lpp_numeric_call coordinates target pre)"
    using edge post by (auto simp: s target lpp_success_atom_eval_def)
qed


lemma lpp_all_numeric_entries_SN:
  assumes entries: "LTS.source ` transition_rules system \<subseteq> lts.initial system"
    and child: "LPPIntegerLTS.lts_termination system"
  shows "SN (LPPIntegerLTS.transition system)"
proof -
  have sn: "SN_on (LPPIntegerLTS.transition system) {s}" for s
  proof (cases "\<exists>t. (s,t)\<in>LPPIntegerLTS.transition system")
    case True
    then obtain t where step: "(s,t)\<in>LPPIntegerLTS.transition system" by blast
    have initial: "s\<in>LPPIntegerLTS.initial_states system"
      using step entries by (auto simp: LPPIntegerLTS.initial_states_def
        elim!: LPPIntegerLTS.mem_transitionE)
    show ?thesis by (rule SN_on_subset2[OF _ child]) (use initial in auto)
  next
    case False
    show ?thesis by (rule step_reflects_SN_on) (use False in blast)
  qed
  show ?thesis using sn by (simp add: SN_defs)
qed

theorem lpp_numeric_component_termination:
  fixes P :: "'v lpp_success_clause list" and row_receipts :: "'v lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_numeric_calls T coordinates locations system D row_receipts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and entries: "LTS.source ` transition_rules system \<subseteq> lts.initial system"
    and child: "LPPIntegerLTS.lts_termination system"
  shows "SN (lpp_observed_calls (set D) P)"
  by (rule lpp_checked_numeric_calls_SN[OF checked transfer lpp_all_numeric_entries_SN[OF entries child]])

ML \<open>
val checked = [@{thm lpp_checked_numeric_call_step}, @{thm lpp_checked_numeric_calls_SN}, @{thm lpp_numeric_component_termination}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric call bridge dependency" else ();
\<close>
end
