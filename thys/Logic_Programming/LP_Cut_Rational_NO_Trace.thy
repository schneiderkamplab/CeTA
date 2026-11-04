theory LP_Cut_Rational_NO_Trace
  imports LP_Cut_Rational_NO_Control
begin

datatype lpc_rational_action = LPCRationalAdmin | LPCRationalCase nat
  | LPCRationalResolve "(string \<times> nat) list" "nat lp_cut_goal list"
  | LPCRationalBacktrack lp_rational_clash

fun lpc_rational_step where
  "lpc_rational_step fuel G P s LPCRationalAdmin t = (lp_cut_admin s=Some t)"
| "lpc_rational_step fuel G P (LPCGoals (LPCAtom i#gs)#es) (LPCRationalCase m) t =
    lpc_rational_case G P i gs es m t"
| "lpc_rational_step fuel G P (LPCClause (LPCAtom i#gs) c m#es) (LPCRationalResolve env body) t =
    lpc_rational_resolve fuel G P i gs c m es env body t"
| "lpc_rational_step fuel G P (LPCClause (LPCAtom i#gs) c m#es) (LPCRationalBacktrack evidence) t =
    (lp_rational_graph_closed G \<and> i<length G \<and> c<length P \<and>
     lp_rational_head_clash fuel G i (fst (P!c)) evidence \<and> t=es)"
| "lpc_rational_step fuel G P s a t = False"

lemma lpc_rational_step_sound:
  "lpc_rational_step fuel G P s a t \<Longrightarrow>
    (lpc_rational_state G s,lpc_rational_state G t)\<in>lp_cut_mgu_source P"
  by (induction fuel G P s a t rule: lpc_rational_step.induct)
    (auto intro: lpc_rational_admin_sound lpc_rational_case_sound
       lpc_rational_resolve_sound lpc_rational_backtrack_sound)

fun lpc_rational_trace where
  "lpc_rational_trace fuel G P s [] t = (s=t)"
| "lpc_rational_trace fuel G P s ((a,u)#steps) t =
    (lpc_rational_step fuel G P s a u \<and> lpc_rational_trace fuel G P u steps t)"

lemma lpc_rational_trace_path:
  "lpc_rational_trace fuel G P s steps t \<Longrightarrow>
    lpc_no_path P (lpc_rational_state G s)
      (map (\<lambda>x. lpc_rational_state G (snd x)) steps)"
  by (induct steps arbitrary: s) (auto intro: lpc_rational_step_sound split: prod.splits)

lemma lpc_rational_trace_last:
  "lpc_rational_trace fuel G P s steps t \<Longrightarrow> last (s#map snd steps)=t"
  by (induct steps arbitrary: s) (auto split: prod.splits)

lemma lpc_rational_safe_map:
  "lpc_no_suffix_safe (lpc_rational_state G s)=lpc_no_suffix_safe s"
  by (cases s rule: lpc_no_suffix_safe.cases) (auto simp: lp_cut_state_map_def)

theorem lpc_rational_trace_pump:
  assumes program: "lp_cut_source_program P"
    and loop: "lpc_rational_trace fuel G P [LPCGoals [LPCAtom i]] steps
      ([LPCGoals [LPCAtom i]]@after)"
    and progress: "steps\<noteq>[]"
    and safe: "list_all (\<lambda>x. lpc_no_suffix_safe (snd x)) steps"
  shows "\<not>SN_on (lp_cut_mgu_source P)
    {lpc_rational_state G [LPCGoals [LPCAtom i]]@before}"
proof -
  let ?core = "lpc_rational_state G [LPCGoals [LPCAtom i]]"
  obtain u us where steps: "map (\<lambda>x. lpc_rational_state G (snd x)) steps=u#us"
    using progress by (cases steps) auto
  have path: "lpc_no_path P ?core (u#us)"
    using lpc_rational_trace_path[OF loop] steps by simp
  have last_refs: "last (map snd steps)=[LPCGoals [LPCAtom i]]@after"
    using lpc_rational_trace_last[OF loop] progress by (cases steps) auto
  have nonempty: "map snd steps\<noteq>[]" using progress by simp
  have last: "last (u#us)=?core@lpc_rational_state G after"
    using last_map[OF nonempty, of "\<lambda>s. lpc_rational_state G s"] last_refs steps
    by (simp add: map_map o_def lp_cut_state_map_def)
  have suffix: "lpc_no_suffix_safe v" if "v\<in>set (?core#u#us)" for v
  proof (cases "v=?core")
    case True then show ?thesis by (simp add: lp_cut_state_map_def)
  next
    case False
    have member: "v\<in>set (map (\<lambda>x. lpc_rational_state G (snd x)) steps)"
      using that False steps by auto
    obtain a s where item: "(a,s)\<in>set steps" and value_eq: "v=lpc_rational_state G s"
      using member by auto
    have "lpc_no_suffix_safe s" using safe item by (auto simp: list_all_iff)
    then show ?thesis by (simp only: value_eq lpc_rational_safe_map)
  qed
  have core: "map (lp_cut_scope_entry r) ?core=?core" for r
    by (simp add: lp_cut_state_map_def)
  show ?thesis by (rule lpc_no_pending_pump[OF program path last suffix core])
qed
end
