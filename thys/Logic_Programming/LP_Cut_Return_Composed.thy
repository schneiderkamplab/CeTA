theory LP_Cut_Return_Composed
  imports LP_Cut_Return_Ground_Split_Check
begin

datatype 'f lpc_return_composed_action =
    LPCRLocal "'f lpc_return_module_action"
  | LPCRSplit "(string \<times> nat) list" "nat list"
      "'f lpc_term lp_cut_goal list" "'f lpc_term lp_cut_goal list" "'f lpc_term list"
      "'f lpc_return_module_data" "'f lpc_link" "string list"
      "'f lpc_return_module_data" "'f lpc_link"
  | LPCRGroundSplit "(string \<times> nat) list" "nat list"
      "'f lpc_term lp_cut_goal list" "'f lpc_term lp_cut_goal list" "'f lpc_term list"
      "'f lpc_return_module_data" "'f lpc_link" "string list"
      "'f lpc_return_module_data" "'f lpc_link" "nat list"
      "('f lp_cut_symbol,string) lp_clause list" "'f list" "'f lp_cut_symbol lp_ground_mode list"

fun lpc_check_return_composed_action where
  "lpc_check_return_composed_action fuel P Q nds states nd ss returned arity (LPCRLocal a) =
    lpc_check_return_module_action fuel P Q nds states nd ss returned arity a"
| "lpc_check_return_composed_action fuel P Q nds states nd ss returned arity
    (LPCRSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link) =
    lpc_check_return_split fuel P Q nd ss returned arity bindings indices pre rest interface
      prefix_module prefix_link vs continuation_module continuation_link"
| "lpc_check_return_composed_action fuel P Q nds states nd ss returned arity
    (LPCRGroundSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes) =
    lpc_check_ground_return_split fuel P Q nd ss returned arity bindings indices pre rest interface
      prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes"

lemma lpc_return_composed_action_sound:
  assumes checked: "lpc_check_return_composed_action fuel P Q nds states nd ss returned arity action"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
    and lower: "\<And>vs v. ([(lpcn_pred nd,map eta (lpcn_vars nd))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lpc_return_module_rep nds states vs v \<Longrightarrow>
      lpc_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
  shows "lpc_return_contract P (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (cases action)
  case (LPCRLocal a)
  show ?thesis by (rule lpc_return_module_action_sound[OF _ known lower]) (use checked LPCRLocal in simp)
next
  case (LPCRSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link)
  show ?thesis by (rule lpc_return_split_checked_contract[OF _ program known sn]) (use checked LPCRSplit in simp)
next
  case (LPCRGroundSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes)
  show ?thesis by (rule lpc_ground_return_split_checked_contract[OF _ program known sn]) (use checked LPCRGroundSplit in simp)
qed

definition lpc_check_return_composed where
  "lpc_check_return_composed fuel P Q nds states returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpc_check_return_composed_action fuel P Q nds states (nds!i) (states!i) returned arity (actions!i)) [0..<length nds])"

theorem lpc_check_return_composed_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_composed fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpc_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (rule lpc_return_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {t} \<and>
      lpc_return_module_rep nds states ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<and>
    lpc_return_module_rep nds states (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding lpc_return_module_rep_def lpc_return_rep_def
    using root known checked residual by (auto simp: lpc_check_return_composed_def intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
      SN_on (lp_ild Q) {t} \<and> lpc_return_module_rep nds states ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {v} \<and>
        lpc_return_module_rep nds states vs v \<Longrightarrow> lpc_return_contract P vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpc_return_module_rep_def lpc_return_rep_def)
  have sn: "SN_on (lp_ild Q) {t}" using represented by simp
  have descendants: "lpc_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    if strict: "(t,v)\<in>(lp_ild Q)\<^sup>+" and rep: "lpc_return_module_rep nds states vs v" for vs v
  proof -
    have child_sn: "SN_on (lp_ild Q) {v}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use trancl_into_rtrancl[OF strict] in auto)
    show ?thesis by (rule lower[OF strict]) (use rep child_sn in auto)
  qed
  have check: "lpc_check_return_composed_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
    using checked bound by (auto simp: lpc_check_return_composed_def list_all_iff)
  have canonical: "lpc_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule lpc_return_composed_action_sound[OF check program knowledge])
      (use sn descendants t in auto)
  have restored: "lpc_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpc_return_contract_scopes[OF program canonical])
  show "lpc_return_contract P ss (lp_ild Q) t out"
    using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
qed

end
