theory LP_Cut_State
  imports LP_Cut_Normalize LP_Cut_Meta LP_Cut_Graph
begin

text \<open>Interpret the entire ordered choice stack, not only its active
goal. Local certificates are checked on finite symbolic states; their coverage
theorems quantify over all runtime valuations, including rational trees.\<close>

fun lp_cut_entry_map where
  "lp_cut_entry_map f (LPCGoals gs) = LPCGoals (map (lp_cut_map f) gs)"
| "lp_cut_entry_map f (LPCClause gs c m) = LPCClause (map (lp_cut_map f) gs) c m"
| "lp_cut_entry_map f (LPCBarrier m) = LPCBarrier m"

definition lp_cut_state_map where
  "lp_cut_state_map f es = map (lp_cut_entry_map f) es"

abbreviation lp_cut_state_eval where
  "lp_cut_state_eval s \<eta> \<equiv> lp_cut_state_map (\<lambda>t. lp_ieval t \<eta>) s"

lemma lp_cut_map_comp:
  "lp_cut_map f (lp_cut_map g a) = lp_cut_map (\<lambda>x. f (g x)) a"
  by (cases a) simp_all

lemma lp_cut_prune_map:
  "lp_cut_state_map f (lp_cut_prune m es) = lp_cut_prune m (lp_cut_state_map f es)"
  by (induct es) (auto simp: lp_cut_state_map_def split: lp_cut_entry.splits)

lemma lp_cut_admin_map:
  "lp_cut_admin (lp_cut_state_map f es) = map_option (lp_cut_state_map f) (lp_cut_admin es)"
proof (induct es rule: lp_cut_admin.induct)
  case (5 g gs es)
  then show ?case
    by (cases g) (simp_all add: lp_cut_state_map_def lp_cut_prune_map[unfolded lp_cut_state_map_def])
qed (simp_all add: lp_cut_state_map_def)

lemma lp_cut_entry_weight_map[simp]:
  "lp_cut_entry_weight (lp_cut_entry_map f e) = lp_cut_entry_weight e"
  by (cases e) simp_all

lemma lp_cut_weight_map:
  "lp_cut_weight (lp_cut_state_map f es) = lp_cut_weight es"
  by (simp add: lp_cut_state_map_def lp_cut_weight_def map_map o_def)

lemma lp_cut_admin_source_unique:
  assumes admin: "lp_cut_admin s=Some t" and step: "(s,u)\<in>lp_cut_source P"
  shows "u=t"
  using step admin by (cases rule: lp_cut_source.cases) auto

definition lp_cut_check_admin where
  "lp_cut_check_admin s t = (lp_cut_admin s=Some t)"

theorem lp_cut_checked_admin_covers:
  assumes checked: "lp_cut_check_admin s t"
    and step: "(lp_cut_state_eval s \<eta>,u)\<in>lp_cut_source P"
  shows "u=lp_cut_state_eval t \<eta> \<and>
    lp_cut_weight u < lp_cut_weight (lp_cut_state_eval s \<eta>)"
proof -
  have admin: "lp_cut_admin (lp_cut_state_eval s \<eta>)=Some (lp_cut_state_eval t \<eta>)"
    using checked by (simp add: lp_cut_check_admin_def lp_cut_admin_map)
  have eq: "u=lp_cut_state_eval t \<eta>"
    by (rule lp_cut_admin_source_unique[OF admin step])
  show ?thesis using lp_cut_admin_decreases[OF admin] eq by simp
qed

lemma lp_cut_checked_admin_step:
  "lp_cut_check_admin s t \<Longrightarrow>
    (lp_cut_state_eval s \<eta>,lp_cut_state_eval t \<eta>)\<in>lp_cut_source P"
  by (rule lp_cut_source.admin) (simp add: lp_cut_check_admin_def lp_cut_admin_map)

lemma cut_does_not_remove_caller_choice:
  "\<not>lp_cut_check_admin
    [LPCGoals [LPCCut 2],LPCBarrier 2,LPCGoals [LPCFail]]
    [LPCGoals [],LPCBarrier 2]"
  by (simp add: lp_cut_check_admin_def)

lemma cut_removes_only_inner_choices:
  "lp_cut_check_admin
    [LPCGoals [LPCCut 2],LPCGoals [LPCTrue],LPCBarrier 2,LPCGoals [LPCFail]]
    [LPCGoals [],LPCBarrier 2,LPCGoals [LPCFail]]"
  by (simp add: lp_cut_check_admin_def)

end
