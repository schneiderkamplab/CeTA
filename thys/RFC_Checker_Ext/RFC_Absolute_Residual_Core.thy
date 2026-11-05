theory RFC_Absolute_Residual_Core
  imports RFC_Matchbounds_Ext
begin

lemma SN_on_union_from_relative_and_global:
  assumes rel: "SN_on (relto R S) X" and weak: "SN S"
  shows "SN_on (R \<union> S) X"
proof
  fix f
  assume start: "f 0 \<in> X" and steps: "chain (R \<union> S) f"
  from relative_ending[OF steps start rel]
  obtain j where tail: "\<forall>i\<ge>j. (f i, f (Suc i)) \<in> S - R" by auto
  have chain: "chain S (shift f j)" using tail by auto
  have all: "\<forall>g. \<exists>i. (g i, g (Suc i)) \<notin> S"
    using weak by (simp add: SN_defs)
  from spec[OF all, of "shift f j"]
  obtain i where "(shift f j i, shift f j (Suc i)) \<notin> S" by blast
  with chain show False by auto
qed

lemma SN_from_RFC_delete_and_absolute_residual:
  fixes D K :: "('f,string)trs"
  assumes wf: "wf_trs (D \<union> K)"
    and rlin: "\<And>lr. lr \<in> D \<union> K \<Longrightarrow> linear_term (snd lr)"
    and sn_rfc: "SN_on (relto (rstep D) (rstep K))
      (right_forw_closure string_rename (D \<union> K))"
    and residual: "SN (rstep K)"
  shows "SN (rstep (D \<union> K))"
proof -
  have "SN_on (rstep D \<union> rstep K)
      (right_forw_closure string_rename (D \<union> K))"
    by (rule SN_on_union_from_relative_and_global[OF sn_rfc residual])
  then have "SN_on (rstep (D \<union> K))
      (right_forw_closure string_rename (D \<union> K))"
    by (simp add: rstep_union)
  with right_linear_SN_rstep_RFC[OF wf rlin, of string_rename]
  show ?thesis by simp
qed

definition rfc_matchbox_absolute_bounds_tt where
  "rfc_matchbox_absolute_bounds_tt I info initial_terms D tp = do {
    tp' \<leftarrow> rfc_matchbox_relative_bounds_tt I info initial_terms D tp;
    return (tp_ops.mk I (tp_ops.nfs I tp') (tp_ops.Q I tp') (tp_ops.R I tp') [])
  }"

lemma rfc_matchbox_absolute_bounds_tt_sound:
  fixes info :: "('f::{linorder,showl,compare_order}, 'q::{compare_order,showl}) bounds_info"
  assumes spec: "tp_spec I"
    and res: "rfc_matchbox_absolute_bounds_tt I info initial_terms D tp = return tp''"
    and inf: "infinite (UNIV :: 'f set)"
    and rec: "SN_qrel (tp_ops.qreltrs I tp'')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by (rule spec)
  obtain tp' where old: "rfc_matchbox_relative_bounds_tt I info initial_terms D tp = return tp'"
    and result: "tp'' = mk (NFS tp') (Q tp') (R tp') []"
    using res unfolding rfc_matchbox_absolute_bounds_tt_def
    by (auto split: sum_bind_splits)
  obtain bi ren where ren: "get_integer_bounds_info info = (bi,ren)" by (cases "get_integer_bounds_info info") auto
  obtain type c qfin preTA rel where bi: "bi = Bounds_Info type c qfin preTA rel" by (cases bi) auto
  from old[unfolded rfc_matchbox_relative_bounds_tt_def ren bi Let_def]
  have q: "Q tp = []" and w: "Rw tp = []" and n: "NFS tp = False"
    and sub: "set D \<subseteq> set (R tp)"
    and wf: "wf_trs (set (R tp))"
    and lin: "list_all (\<lambda>(l,r). linear_term r) (R tp)"
    and out: "tp' = mk (NFS tp) (Q tp) (ceta_list_diff (R tp) D) D"
    by (auto simp: Q_empty_sound isOK_check_allm split: if_splits sum_bind_splits)
  have ok: "isOK (rfc_matchbox_relative_bounds_tt I info initial_terms D tp)" using old by simp
  have union: "set D \<union> set (ceta_list_diff (R tp) D) = set (R tp)" using sub by auto
  have residual: "SN (rstep (set (ceta_list_diff (R tp) D)))"
    using rec unfolding result out qreltrs_sound SN_qrel_def split n q by simp
  have rfc: "SN_on (relto (rstep (set D)) (rstep (set (ceta_list_diff (R tp) D))))
      (right_forw_closure string_rename (set D \<union> set (ceta_list_diff (R tp) D)))"
    using rfc_matchbox_relative_bounds_SN_on[OF spec ok inf]
    unfolding rfc_forward_closure_eq union .
  have wfDK: "wf_trs (set D \<union> set (ceta_list_diff (R tp) D))"
    unfolding union by (rule wf)
  have linDK: "\<And>lr. lr \<in> set D \<union> set (ceta_list_diff (R tp) D) \<Longrightarrow> linear_term (snd lr)"
    unfolding union using lin by (auto simp: list_all_iff split: prod.splits)
  have "SN (rstep (set D \<union> set (ceta_list_diff (R tp) D)))"
    by (rule SN_from_RFC_delete_and_absolute_residual[OF wfDK linDK rfc residual])
  then show ?thesis unfolding union qreltrs_sound SN_qrel_def split n q w by simp
qed

end
