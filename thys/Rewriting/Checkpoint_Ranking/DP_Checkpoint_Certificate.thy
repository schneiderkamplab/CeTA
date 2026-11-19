theory DP_Checkpoint_Certificate
 imports DP_Checkpoint_Transition
begin

fun checkpoint_selected_forest where
 "checkpoint_selected_forest C N Z S coord_map (Var x) = []"
| "checkpoint_selected_forest C N Z S coord_map (Fun f ts) =
 checkpoint_forest N Z S (checkpoint_skeleton C (ts!(coord_map f)))"

definition checkpoint_selected_rank where
 "checkpoint_selected_rank C L N Z S coord_map t =
 (Inr (map (checkpoint_rank_view L) (checkpoint_selected_forest C N Z S coord_map t))
 ::('f+unit,unit) term + ('f+unit,unit) term list)"

definition check_checkpoint_annotation_table where
 "check_checkpoint_annotation_table U K coord_map table =
 list_all (\<lambda>(f,n,clause). f\<in>U \<and>
 list_all (checkpoint_atom_bounded n) clause \<and>
 (f\<in>K \<longrightarrow> coord_map f<n \<and> CP_Strict (coord_map f)\<in>set clause)) table"

lemma checkpoint_annotation_table_root:
 assumes checked: "check_checkpoint_annotation_table U K coord_map table"
 and holds: "checkpoint_annotation_holds C L N Z S R table old t"
 obtains f ts where "t=Fun f ts" "f\<in>U"
 using checked holds
 by (cases t) (auto simp: checkpoint_annotation_holds_def check_checkpoint_annotation_table_def list_all_iff list_ex_iff)

lemma checkpoint_annotation_table_entry:
 assumes checked: "check_checkpoint_annotation_table U K coord_map table"
 and member: "(f,n,clause)\<in>set table"
 shows "f\<in>U \<and> list_all (checkpoint_atom_bounded n) clause \<and>
 (f\<in>K \<longrightarrow> coord_map f<n \<and> CP_Strict (coord_map f)\<in>set clause)"
 using bspec[OF checked[unfolded check_checkpoint_annotation_table_def list_all_iff] member]
 by (simp add: list_all_iff)

lemma checkpoint_annotation_table_boundary:
 assumes checked: "check_checkpoint_annotation_table U K coord_map table"
 and marked: "checkpoint_at K t"
 and holds: "checkpoint_annotation_holds C L N Z S R table old t"
 shows "checkpoint_forest_less L (checkpoint_selected_forest C N Z S coord_map t) old"
proof -
 obtain f ts where t: "t=Fun f ts" and root: "f\<in>U"
 by (rule checkpoint_annotation_table_root[OF checked holds])
 obtain clause where member: "(f,length ts,clause)\<in>set table"
 and initial: "checkpoint_clause_holds C L N Z S R old clause ts"
 using holds by (auto simp: checkpoint_annotation_holds_def t list_ex_iff)
 have strict: "CP_Strict (coord_map f)\<in>set clause"
 using checkpoint_annotation_table_entry[OF checked member] marked by (simp add: t)
 have atom: "checkpoint_atom_holds C L N Z S R old (CP_Strict (coord_map f)) ts"
 using initial strict by (auto simp: checkpoint_clause_holds_def list_all_iff)
 show ?thesis using atom by (simp add: t)
qed

lemma checkpoint_annotation_table_support:
 assumes table: "check_checkpoint_annotation_table U K coord_map annotation"
 and safe: "checkpoint_skeleton_safe C R"
 and roots: "\<And>l r. (l,r)\<in>R \<Longrightarrow> checkpoint_opaque_root U l"
 and holds: "checkpoint_annotation_holds C L N Z S R annotation old s"
 and steps: "(s,t)\<in>(Trs.rstep R)\<^sup>*"
 shows "checkpoint_annotation_holds C L N Z S R annotation old t"
proof -
 obtain f ss where s: "s=Fun f ss" and root: "f\<in>U"
 by (rule checkpoint_annotation_table_root[OF table holds])
 show ?thesis by (rule checkpoint_annotation_transport[OF safe _ root steps[unfolded s] holds[unfolded s]]) (use roots in blast)
qed

lemma checkpoint_coverage_lhs:
 assumes covered: "check_checkpoint_transition_coverage K coord_map pair_list table receipts"
 and index: "i<length pair_list"
 obtains f ss where "fst (pair_list!i)=Fun f ss"
 using checkpoint_coverage_at[OF covered index] by (cases "fst (pair_list!i)") auto


lemma checked_checkpoint_certificate:
 fixes pair_list support :: "('f,'v) rule list"
 and nfs minimal :: bool
 assumes control: "check_checkpoint_control U K height_map pair_list support"
 and safe: "checkpoint_skeleton_safe C (set support)"
 and table: "check_checkpoint_annotation_table U K coord_map annotation"
 and checked: "list_all (check_checkpoint_transition checker pair_list annotation) receipts"
 and covered: "check_checkpoint_transition_coverage K coord_map pair_list annotation receipts"
 and sound: "\<And>old sigma known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S (set support) old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S (set support) old sigma claim"
 shows "finite_dpp (nfs,minimal,set pair_list,{},{},{},set support)"
proof -
 have roots: "\<And>l r. (l,r)\<in>set support \<Longrightarrow> checkpoint_opaque_root U l"
 using control by (auto simp: check_checkpoint_control_def list_all_iff checkpoint_support_control_correct)
 let ?A = "\<lambda>origin. checkpoint_annotation_holds C L N Z S (set support) annotation
 (checkpoint_selected_forest C N Z S coord_map origin)"
 show ?thesis
 proof (rule checked_checkpoint_path_ranking[OF control lpp_forest_call_order_wf,
  where A="?A" and rank="checkpoint_selected_rank C L N Z S coord_map"])
  fix origin :: "('f,'v) term" assume marked: "checkpoint_at K origin"
  show "list_all (checkpoint_rule_contract (set support) (\<lambda>s. s= origin) (?A origin)) pair_list"
  unfolding list_all_iff
  proof (intro ballI)
   fix pair assume member: "pair\<in>set pair_list"
   obtain i where index: "i<length pair_list" and pair: "pair_list!i= pair"
    using member by (auto simp: in_set_conv_nth)
   obtain f ss where left: "fst (pair_list!i)=Fun f ss"
    by (rule checkpoint_coverage_lhs[OF covered index])
   show "checkpoint_rule_contract (set support) (\<lambda>s. s= origin) (?A origin) pair"
   unfolding checkpoint_rule_contract_def
   proof (intro allI impI)
    fix sigma t
    assume source: "fst pair\<cdot>sigma= origin"
    and steps: "(snd pair\<cdot>sigma,t)\<in>(Trs.rstep (set support))\<^sup>*"
    have origin: "origin=Fun f (map (\<lambda>t. t\<cdot>sigma) ss)" using source left by (simp add: pair)
    have marked_f: "f\<in>K" using marked by (simp add: origin)
    have bound: "coord_map f<length ss" by (rule checkpoint_entry_coverage(1)[OF covered index left marked_f])
    have entry: "checkpoint_annotation_holds C L N Z S (set support) annotation
     (checkpoint_forest N Z S (checkpoint_skeleton C ((ss!(coord_map f))\<cdot>sigma)))
     (snd (pair_list!i)\<cdot>sigma)"
     by (rule checked_checkpoint_entry_transition[OF sound checked covered index left marked_f])
    have after: "?A origin (snd pair\<cdot>sigma)" using entry by (simp add: pair origin bound)
    show "?A origin t" by (rule checkpoint_annotation_table_support[OF table safe roots after steps])
   qed
  qed
 next
  fix origin :: "('f,'v) term"
  show "list_all (checkpoint_rule_contract (set support) (\<lambda>s. ?A origin s \<and> \<not>checkpoint_at K s) (?A origin)) pair_list"
  unfolding list_all_iff
  proof (intro ballI)
   fix pair assume member: "pair\<in>set pair_list"
   obtain i where index: "i<length pair_list" and pair: "pair_list!i= pair"
    using member by (auto simp: in_set_conv_nth)
   obtain f ss where left: "fst (pair_list!i)=Fun f ss"
    by (rule checkpoint_coverage_lhs[OF covered index])
   show "checkpoint_rule_contract (set support) (\<lambda>s. ?A origin s \<and> \<not>checkpoint_at K s) (?A origin) pair"
   unfolding checkpoint_rule_contract_def
   proof (intro allI impI)
    fix sigma t
    assume source: "?A origin (fst pair\<cdot>sigma) \<and> \<not>checkpoint_at K (fst pair\<cdot>sigma)"
    and steps: "(snd pair\<cdot>sigma,t)\<in>(Trs.rstep (set support))\<^sup>*"
    have unmarked: "f\<notin>K" using source left by (simp add: pair)
    have initial: "?A origin (fst (pair_list!i)\<cdot>sigma)" using source by (simp add: pair)
    have entry: "?A origin (snd (pair_list!i)\<cdot>sigma)"
     by (rule checked_checkpoint_internal_transition[OF sound checked covered index left unmarked initial])
    have after: "?A origin (snd pair\<cdot>sigma)" using entry by (simp add: pair)
    show "?A origin t" by (rule checkpoint_annotation_table_support[OF table safe roots after steps])
   qed
  qed
 next
  fix origin t :: "('f,'v) term"
  assume start: "checkpoint_at K origin" and marked: "checkpoint_at K t" and holds: "?A origin t"
  show "(checkpoint_selected_rank C L N Z S coord_map t,checkpoint_selected_rank C L N Z S coord_map origin)\<in>lpp_forest_call_order"
   using checkpoint_annotation_table_boundary[OF table marked holds]
   by (simp add: checkpoint_selected_rank_def checkpoint_forest_less_def)
 qed
qed

ML \<open>
val thms = @{thms checkpoint_annotation_table_root checkpoint_annotation_table_boundary checkpoint_annotation_table_support checkpoint_coverage_lhs checked_checkpoint_certificate};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted annotation certificate interfaces" else ();
\<close>
end
