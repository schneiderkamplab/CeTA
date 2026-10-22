theory LP_Cut_Control
  imports "Proof_Checker.Ceta"
begin

text \<open>Ordered alternatives and scoped cuts from the concrete TPLP'10
semantics. Atom resolution is a separate transition: administrative steps
alone cannot constitute an infinite computation. This theory is infrastructure,
not an accepting source termination checker. In particular it does not justify
transferring nontermination from a program with cuts erased.\<close>

datatype 'a lp_cut_goal = LPCAtom 'a | LPCCut nat | LPCTrue | LPCFail
  | LPCMeta 'a | LPCExpand 'a nat | LPCUnify 'a 'a
datatype 'a lp_cut_entry =
    LPCGoals "'a lp_cut_goal list"
  | LPCClause "'a lp_cut_goal list" nat nat
  | LPCBarrier nat

fun lp_cut_prune where
  "lp_cut_prune m [] = []"
| "lp_cut_prune m (e # es) =
    (case e of LPCBarrier n \<Rightarrow> if m=n then e#es else lp_cut_prune m es
     | _ \<Rightarrow> lp_cut_prune m es)"

fun lp_cut_admin where
  "lp_cut_admin [] = None"
| "lp_cut_admin (LPCBarrier m # es) = Some es"
| "lp_cut_admin (LPCClause gs c m # es) = None"
| "lp_cut_admin (LPCGoals [] # es) = Some es"
| "lp_cut_admin (LPCGoals (g#gs) # es) =
   (case g of LPCAtom a \<Rightarrow> None
    | LPCTrue \<Rightarrow> Some (LPCGoals gs # es)
    | LPCFail \<Rightarrow> Some es
    | LPCCut m \<Rightarrow> Some (LPCGoals gs # lp_cut_prune m es)
    | _ \<Rightarrow> None)"

fun lp_cut_entry_weight where
  "lp_cut_entry_weight (LPCGoals gs) = Suc (length gs)"
| "lp_cut_entry_weight (LPCClause gs c m) = Suc (length gs)"
| "lp_cut_entry_weight (LPCBarrier m) = 1"

definition lp_cut_weight where
  "lp_cut_weight es = sum_list (map lp_cut_entry_weight es)"

lemma lp_cut_prune_weight:
  "lp_cut_weight (lp_cut_prune m es) \<le> lp_cut_weight es"
  by (induct es) (auto simp: lp_cut_weight_def split: lp_cut_entry.splits if_splits)

lemma lp_cut_admin_decreases:
  "lp_cut_admin s = Some t \<Longrightarrow> lp_cut_weight t < lp_cut_weight s"
proof (induct s rule: lp_cut_admin.induct)
  case (5 g gs es)
  show ?case
  proof (cases g)
    case (LPCCut m)
    have bound: "lp_cut_weight (lp_cut_prune m es) \<le> lp_cut_weight es"
      by (rule lp_cut_prune_weight)
    have t: "t = LPCGoals gs # lp_cut_prune m es"
      using 5 LPCCut by simp
    show ?thesis using bound
      by (simp add: t lp_cut_weight_def; arith)
  qed (use 5 in \<open>auto simp: lp_cut_weight_def\<close>)
qed (auto simp: lp_cut_weight_def)

theorem lp_cut_admin_terminates:
  "SN {(s,t). lp_cut_admin s = Some t}"
proof -
  have subset: "{(s,t). lp_cut_admin s = Some t} \<subseteq> (measure lp_cut_weight)\<inverse>"
    using lp_cut_admin_decreases by auto
  have sn: "SN ((measure lp_cut_weight)\<inverse>)"
    by (simp add: SN_iff_wf)
  show ?thesis by (rule SN_subset[OF sn subset])
qed

lemma lp_cut_keeps_caller:
  "lp_cut_prune m (LPCBarrier m # caller) = LPCBarrier m # caller"
  by simp

lemma lp_cut_crosses_nested_barrier:
  "m \<noteq> n \<Longrightarrow> lp_cut_prune m (LPCBarrier n # es) = lp_cut_prune m es"
  by simp

end
