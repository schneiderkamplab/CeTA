theory Higher_Order_CeTA_Check
  imports "Higher_Order_CeTA_Delegation.Higher_Order_CeTA_Delegation"
begin

hide_const (open) CPF_Proof_Parser.rstep


definition ho_fo_symbol where
  "ho_fo_symbol c = UnLab (replicate c CHR ''f'' @ ''s'')"

fun ho_to_fo_term :: "ho_fo_tree \<Rightarrow> ((string,label_type) lab,string) term" where
  "ho_to_fo_term (HFOVar n) = term.Var (replicate n CHR ''x'' @ ''v'')"
| "ho_to_fo_term (HFOFun c ts) = term.Fun (ho_fo_symbol c) (map ho_to_fo_term ts)"

lemma ho_to_fo_substitution:
  "ho_to_fo_term (ho_fo_substitution s t) =
    ho_to_fo_term t \<cdot> (\<lambda>v. ho_to_fo_term (s (length v - 1)))"
  by (induction t) (auto simp: map_map o_def cong: map_cong)

definition ho_delegation_trs where
  "ho_delegation_trs P ce =
    map (\<lambda>(p,q). (ho_to_fo_term p,ho_to_fo_term q)) P @
      [(term.Fun (ho_fo_symbol ce) [term.Var ''v'',term.Var ''xv''],term.Var ''v''),
       (term.Fun (ho_fo_symbol ce) [term.Var ''v'',term.Var ''xv''],term.Var ''xv'')]"

definition ho_delegation_step where
  "ho_delegation_step P ce t u \<longleftrightarrow>
    (ho_to_fo_term t,ho_to_fo_term u)\<in>rstep (set (ho_delegation_trs P ce))"

lemma ho_delegation_ce_left:
  "ho_delegation_step P ce (HFOFun ce [x,y]) x"
proof -
  have rule: "(term.Fun (ho_fo_symbol ce) [term.Var ''v'',term.Var ''xv''],term.Var ''v'')\<in>set (ho_delegation_trs P ce)"
    by (simp add: ho_delegation_trs_def)
  note step = rstep_subst[OF rstep_rule[OF rule],
    of "\<lambda>n. if n=''v'' then ho_to_fo_term x else ho_to_fo_term y"]
  show ?thesis using step by (simp add: ho_delegation_step_def)
qed

lemma ho_delegation_ce_right:
  "ho_delegation_step P ce (HFOFun ce [x,y]) y"
proof -
  have rule: "(term.Fun (ho_fo_symbol ce) [term.Var ''v'',term.Var ''xv''],term.Var ''xv'')\<in>set (ho_delegation_trs P ce)"
    by (simp add: ho_delegation_trs_def)
  note step = rstep_subst[OF rstep_rule[OF rule],
    of "\<lambda>n. if n=''v'' then ho_to_fo_term x else ho_to_fo_term y"]
  show ?thesis using step by (simp add: ho_delegation_step_def)
qed

lemma ho_delegation_context:
  assumes "ho_delegation_step P ce x y"
  shows "ho_delegation_step P ce (HFOFun c (xs@x#ys)) (HFOFun c (xs@y#ys))"
  using rstep_ctxt[of "ho_to_fo_term x" "ho_to_fo_term y"
    "set (ho_delegation_trs P ce)" "More (ho_fo_symbol c) (map ho_to_fo_term xs) \<box> (map ho_to_fo_term ys)"]
    assms by (simp add: ho_delegation_step_def)

lemma ho_delegation_instance:
  assumes "(p,q)\<in>set P"
  shows "ho_delegation_step P ce (ho_fo_substitution s p) (ho_fo_substitution s q)"
proof -
  have rule: "(ho_to_fo_term p,ho_to_fo_term q)\<in>set (ho_delegation_trs P ce)"
    using assms by (auto simp: ho_delegation_trs_def)
  show ?thesis unfolding ho_delegation_step_def ho_to_fo_substitution
    by (rule rstep_subst[OF rstep_rule[OF rule]])
qed

lemma ho_delegation_wf:
  assumes sn: "SN (rstep (set (ho_delegation_trs P ce)))"
  shows "wf {(u,t). (ho_delegation_step P ce)\<^sup>+\<^sup>+ t u}"
proof -
  have sn': "SN (inv_image (rstep (set (ho_delegation_trs P ce))) ho_to_fo_term)"
    by (rule SN_inv_image[OF sn])
  have eq: "{(t,u). ho_delegation_step P ce t u} =
    inv_image (rstep (set (ho_delegation_trs P ce))) ho_to_fo_term"
    by (auto simp: ho_delegation_step_def inv_image_def)
  have wf: "wf (({(t,u). ho_delegation_step P ce t u}\<^sup>+)\<inverse>)"
    using SN_imp_SN_trancl[OF sn'] unfolding SN_iff_wf eq .
  show ?thesis using wf by (simp add: trancl_def converse_def)
qed

definition ho_check_ceta_delegation where
  "ho_check_ceta_delegation I J S R F P ce ranks arities priorities sorts fuel prf =
    (ho_check_delegation_side S R F P ranks arities priorities sorts fuel \<and>
      isOK (check_trs_termination_proof I J False id
        (tp_ops.mk I False [] (ho_delegation_trs P ce) []) prf))"

theorem ho_check_ceta_delegation_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "ho_check_ceta_delegation I J S R F P ce ranks arities priorities sorts fuel prf"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  interpret tp_spec I by (rule I)
  have side: "ho_check_delegation_side S R F P ranks arities priorities sorts fuel"
    and child_ok: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (ho_delegation_trs P ce) []) prf)"
    using checked by (auto simp: ho_check_ceta_delegation_def)
  have sn: "SN (rstep (set (ho_delegation_trs P ce)))"
    using check_trs_termination_proof[OF I J child_ok]
    by (simp add: SN_qrel_def)
  show ?thesis
    by (rule ho_check_delegation_side_sound[
      where rel="ho_delegation_step P ce" and ce=ce,
      OF side ho_delegation_ce_left ho_delegation_ce_right
        ho_delegation_context ho_delegation_instance ho_delegation_wf[OF sn]])
qed

definition ho_check_ceta_delegation_xml where
  "ho_check_ceta_delegation_xml S R F P ce ranks arities priorities sorts fuel xml =
    (case parse_xml_string
      (xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty) xml of
       Right prf \<Rightarrow> ho_check_ceta_delegation tp_rbt_impl dpp_rbt_impl
         S R F P ce ranks arities priorities sorts fuel prf
     | _ \<Rightarrow> False)"

theorem ho_check_ceta_delegation_xml_sound:
  assumes "ho_check_ceta_delegation_xml S R F P ce ranks arities priorities sorts fuel xml"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  obtain child where child_check:
    "ho_check_ceta_delegation tp_rbt_impl dpp_rbt_impl
       S R F P ce ranks arities priorities sorts fuel child"
    using assms unfolding ho_check_ceta_delegation_xml_def
    by (cases "parse_xml_string
      (xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty) xml") auto
  show ?thesis
    by (rule ho_check_ceta_delegation_sound[OF tp_rbt_impl dpp_rbt_impl child_check])
qed

end
