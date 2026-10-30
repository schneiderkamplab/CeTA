theory LP_Prolog_Context_References
 imports LP_Prolog_Context_Module_Semantics
begin

datatype lpp_context_reference_action = LPPCRLocal lpp_context_module_action
  | LPPCRSplit "(string \<times> nat) list" "nat list"
      "string lpc_term lp_cut_goal list" "string lpc_term lp_cut_goal list" "string lpc_term list"
      nat "string lpc_link" "string list"
      nat "string lpc_link"

fun lpp_context_reference_types where
  "lpp_context_reference_types (LPPCRLocal action) = lpp_context_module_types action"
| "lpp_context_reference_types (LPPCRSplit bindings indices pre rest interface pm pe vs cm ce) = []"

fun lpp_check_context_reference_action where
  "lpp_check_context_reference_action fuel P Q T modules nds states contexts nd ss context returned arity (LPPCRLocal action) =
    lpp_check_context_module_action fuel P Q nds states contexts nd ss context returned arity action"
| "lpp_check_context_reference_action fuel P Q T modules nds states contexts nd ss context returned arity
      (LPPCRSplit bindings indices pre rest interface pm pe vs cm ce) =
    (pm < length modules \<and> cm < length modules \<and>
     lpp_check_context_split_interface fuel P Q T nd ss context returned arity
       bindings indices pre rest interface (modules!pm) pe vs (modules!cm) ce)"

lemma lpp_context_reference_action_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_reference_action fuel P Q T modules nds states contexts nd ss context returned arity action"
    and references: "list_all (lpp_context_data_semantics SP P Q) modules"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP context eta"
    and integers: "lpp_integer_known (lpp_context_reference_types action) eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpp_context_module_rep SP nds states contexts vs v \<Longrightarrow>
      lp_answer_contract (lpp_integer_answers P) vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPPCRLocal a)
  show ?thesis by (rule lpp_context_module_action_domain_contract[OF _ known observed _ lower])
    (use checked integers LPPCRLocal in auto)
next
  case (LPPCRSplit bindings indices pre rest interface pm pe vs cm ce)
  show ?thesis by (rule lpp_context_semantic_split_contract[OF _ _ _ transfer program known observed sn])
    (use checked references LPPCRSplit in \<open>auto simp: list_all_iff\<close>)
qed

definition lpp_check_context_reference where
  "lpp_check_context_reference fuel P Q modules nds states contexts T typings returned arity actions =
    (length nds = length states \<and> length nds = length actions \<and>
     length nds = length contexts \<and> length nds = length typings \<and>
     list_all (\<lambda>i. map fst (states!i) = lpcn_state (nds!i) \<and>
       lpp_check_context_typing T (contexts!i) (typings!i) (lpp_context_reference_types (actions!i)) \<and>
       lpp_check_context_reference_action fuel P Q T modules nds states contexts (nds!i) (states!i) (contexts!i) returned arity (actions!i)) [0..<length nds])"

theorem lpp_context_reference_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_reference fuel P Q modules nds states contexts T typings returned arity actions"
    and references: "list_all (lpp_context_data_semantics SP P Q) modules"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (rule lp_answer_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out = (\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {t} \<and>
    lpp_context_module_rep SP nds states contexts ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])]) = (\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<and>
    lpp_context_module_rep SP nds states contexts (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding lpp_context_module_rep_def lpp_context_return_rep_def
    using root known checked observed residual by (auto simp: lpp_check_context_reference_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm)\<Rightarrow>
    (string lp_cut_symbol\<times>(string lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out = (\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {t} \<and>
      lpp_context_module_rep SP nds states contexts ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret = (\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {v} \<and>
      lpp_context_module_rep SP nds states contexts vs v \<Longrightarrow>
      lp_answer_contract (lpp_integer_answers P) vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss = lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and facts: "lpp_source_context_holds SP (contexts!j) nu"
    and t: "t = [(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpp_context_module_rep_def lpp_context_return_rep_def)
  have sn: "SN_on (lp_ild Q) {t}" using represented by simp
  have descendants: "lp_answer_contract (lpp_integer_answers P) vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    if strict: "(t,v)\<in>(lp_ild Q)\<^sup>+" and rep: "lpp_context_module_rep SP nds states contexts vs v" for vs v
  proof -
    have child_sn: "SN_on (lp_ild Q) {v}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use trancl_into_rtrancl[OF strict] in auto)
    show ?thesis by (rule lower[OF strict]) (use child_sn rep in auto)
  qed
  have check: "lpp_check_context_reference_action fuel P Q T modules nds states contexts (nds!j) (states!j) (contexts!j) returned arity (actions!j)"
    and typing: "lpp_check_context_typing T (contexts!j) (typings!j) (lpp_context_reference_types (actions!j))"
    using checked bound by (auto simp: lpp_check_context_reference_def list_all_iff)
  have integers: "lpp_integer_known (lpp_context_reference_types (actions!j)) nu"
    by (rule lpp_context_typing_sound[OF transfer typing facts])
  have canonical: "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval nu (states!j)) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule lpp_context_reference_action_contract[OF check references transfer program knowledge facts integers])
      (use sn descendants t in auto)
  have restored: "lp_answer_contract (lpp_integer_answers P)
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_domain_contract_scopes[OF program canonical])
  show "lp_answer_contract (lpp_integer_answers P) ss (lp_ild Q) t out"
    using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
qed

datatype lpp_reference_module = LPPReferenceModule lpp_context_module_data "lpp_context_reference_action list"

fun lpp_reference_data where
  "lpp_reference_data (LPPReferenceModule m actions) = m"

fun lpp_check_reference_module where
  "lpp_check_reference_module fuel P Q T modules (LPPReferenceModule m actions) =
    lpp_check_context_reference fuel P Q modules (lppcm_nodes m) (lppcm_states m)
      (lppcm_contexts m) T (lppcm_typings m) (lppcm_returned m) (lppcm_arity m) actions"

lemma lpp_reference_module_semantics:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_reference_module fuel P Q T modules m"
    and references: "list_all (lpp_context_data_semantics SP P Q) modules"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
  shows "lpp_context_data_semantics SP P Q (lpp_reference_data m)"
proof (cases m)
  case (LPPReferenceModule data actions)
  show ?thesis unfolding LPPReferenceModule lpp_reference_data.simps lpp_context_data_semantics_def
    using lpp_context_reference_contract[OF _ references transfer _ program]
      checked by (auto simp: LPPReferenceModule)
qed

text \<open>References address modules in the strict tail. Shared dependencies
are checked once, and every referenced contract is established before use.
Cycles inside a module remain obligations of its residual termination proof.\<close>
fun lpp_check_reference_modules where
  "lpp_check_reference_modules fuel P Q T [] = True"
| "lpp_check_reference_modules fuel P Q T (m#ms) =
    (lpp_check_reference_modules fuel P Q T ms \<and>
     lpp_check_reference_module fuel P Q T (map lpp_reference_data ms) m)"

theorem lpp_reference_modules_semantics:
  assumes checked: "lpp_check_reference_modules fuel P Q T modules"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
  shows "list_all (lpp_context_data_semantics SP P Q) (map lpp_reference_data modules)"
  using checked
proof (induction modules)
  case Nil then show ?case by simp
next
  case (Cons m ms)
  have tail: "list_all (lpp_context_data_semantics SP P Q) (map lpp_reference_data ms)"
    using Cons by simp
  have head: "lpp_context_data_semantics SP P Q (lpp_reference_data m)"
    by (rule lpp_reference_module_semantics[where fuel=fuel, OF _ tail transfer program]) (use Cons.prems in simp)
  show ?case using head tail by simp
qed

end
