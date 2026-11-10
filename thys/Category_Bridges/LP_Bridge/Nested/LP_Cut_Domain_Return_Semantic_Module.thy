theory LP_Cut_Domain_Return_Semantic_Module
 imports Category_LP_Cut_Composition_Bridge.LP_Cut_Domain_Return_Composed_Triples
begin

context cut_runtime_domain
begin

theorem precise_return_table_semantic_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes local: "\<And>j nu. j<length nds \<Longrightarrow>
      knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu \<Longrightarrow>
      SN_on (lp_ild Q) {[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]} \<Longrightarrow>
      (\<And>vs v. ([(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
        precise_return_module_rep nds states vs v \<Longrightarrow>
        precise_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])) \<Longrightarrow>
      precise_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q)
        [(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
    and lengths: "length nds=length states"
    and program: "lp_cut_source_program P" and root: "i<length nds"
    and known: "knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "precise_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof (rule precise_return_contract_modular[OF residual, where rep="\<lambda>ss t out.
    out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {t} \<and>
      precise_return_module_rep nds states ss t"])
  show "(\<lambda>rho. [(returned,map rho [0..<arity])])=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
    SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<and>
    precise_return_module_rep nds states (lpc_return_eval eta (states!i)) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    unfolding precise_return_module_rep_def precise_return_rep_def
    using root known residual lengths by (auto intro!: exI[of _ "[]"] exI[of _ i] exI[of _ eta])
next
  fix ss t and out :: "(nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) \<Rightarrow> ('f lp_cut_symbol \<times> ('f lp_cut_symbol,string) lp_iterm list) list"
  assume represented: "out=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and>
      SN_on (lp_ild Q) {t} \<and> precise_return_module_rep nds states ss t"
    and lower: "\<And>vs v ret. (t,v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      ret=(\<lambda>rho. [(returned,map rho [0..<arity])]) \<and> SN_on (lp_ild Q) {v} \<and>
        precise_return_module_rep nds states vs v \<Longrightarrow> precise_return_contract P vs (lp_ild Q) v ret"
  obtain swaps j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps ss=lpc_return_eval nu (states!j)"
    and knowledge: "knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: precise_return_module_rep_def precise_return_rep_def)
  have sn: "SN_on (lp_ild Q) {t}" using represented by simp
  have descendants: "precise_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(returned,map rho [0..<arity])])"
    if strict: "(t,v)\<in>(lp_ild Q)\<^sup>+" and rep: "precise_return_module_rep nds states vs v" for vs v
  proof -
    have child_sn: "SN_on (lp_ild Q) {v}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use trancl_into_rtrancl[OF strict] in auto)
    show ?thesis by (rule lower[OF strict]) (use rep child_sn in auto)
  qed
  have canonical: "precise_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding t by (rule local[OF bound knowledge])
      (use sn descendants t in auto)
  have restored: "precise_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule precise_return_contract_scopes[OF program canonical])
  show "precise_return_contract P ss (lp_ild Q) t out"
    using restored represented by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
qed



end
end
