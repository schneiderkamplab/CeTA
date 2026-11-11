theory LP_Prolog_Checked_Builtin_Trace
 imports LP_Prolog_Integer_NO
begin

text \<open>Shared ordered trace pumping for any locally checked subset of the
existing source transitions. The checker retains saved alternatives and scope
barriers; its operation parameter does not define another operational semantics.\<close>

fun lpp_checked_builtin_trace where
  "lpp_checked_builtin_trace step_check s [] t = (s=t)"
| "lpp_checked_builtin_trace step_check s ((action,u)#rest) t =
    (step_check s action u \<and> lpp_checked_builtin_trace step_check u rest t)"

locale lpp_builtin_trace_checker =
 fixes P U step_check
 assumes step_sound: "\<And>s action t. step_check s action t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>lpp_builtin_source P U"
begin

lemma trace_sound:
  "lpp_checked_builtin_trace step_check s steps t \<Longrightarrow>
   (lp_cut_state_eval s LPIVar,lp_cut_state_eval t LPIVar)\<in>(lpp_builtin_source P U)\<^sup>*"
proof (induct steps arbitrary: s)
  case Nil then show ?case by simp
next
  case (Cons entry rest)
  obtain action u where entry: "entry=(action,u)" by (cases entry) auto
  have step: "(lp_cut_state_eval s LPIVar,lp_cut_state_eval u LPIVar)\<in>lpp_builtin_source P U"
    using Cons.prems entry by (auto intro: step_sound)
  have tail: "(lp_cut_state_eval u LPIVar,lp_cut_state_eval t LPIVar)\<in>(lpp_builtin_source P U)\<^sup>*"
    using Cons.hyps Cons.prems entry by auto
  show ?case using step tail by (meson r_into_rtrancl rtrancl_trans)
qed

lemma trace_path:
  assumes program: "lp_cut_source_program P" and trace: "lpp_checked_builtin_trace step_check s steps t"
  shows "lp_barrier_execution.path (lpp_builtin_source P U) (lp_cut_state_eval s LPIVar)
     (map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps)"
proof -
  interpret source: lp_barrier_execution "lpp_builtin_source P U"
    by (rule lpp_builtin_barrier_execution[OF program])
  from trace show ?thesis
    by (induct steps arbitrary: s) (auto intro: step_sound split: prod.splits)
qed

lemma trace_last:
  "lpp_checked_builtin_trace step_check s steps t \<Longrightarrow> last (s # map snd steps) = t"
  by (induct steps arbitrary: s) (auto split: prod.splits)

lemma trace_pump:
  assumes program: "lp_cut_source_program P"
    and loop: "lpp_checked_builtin_trace step_check [LPCGoals [LPCAtom a]] steps
      ([LPCGoals [LPCAtom a]] @ after)"
    and progress: "steps \<noteq> []"
    and suffix: "lp_cut_barriers after \<and> lp_cut_barriers before"
  shows "\<not> SN_on (lpp_builtin_source P U)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
proof -
  interpret source: lp_barrier_execution "lpp_builtin_source P U"
    by (rule lpp_builtin_barrier_execution[OF program])
  let ?core = "lp_cut_state_eval [LPCGoals [LPCAtom a]] LPIVar"
  obtain u us where steps: "map (\<lambda>x. lp_cut_state_eval (snd x) LPIVar) steps = u#us"
    using progress by (cases steps) auto
  have path: "source.path ?core (u#us)"
    using trace_path[OF program loop] steps by simp
  have nonempty: "map snd steps \<noteq> []" using progress by simp
  have last_finite: "last (map snd steps) = [LPCGoals [LPCAtom a]] @ after"
    using trace_last[OF loop] progress by (cases steps) auto
  have last_mapped: "last (map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps)) =
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
    using last_map[OF nonempty, of "\<lambda>s. lp_cut_state_eval s LPIVar"] last_finite by simp
  have last: "last (u#us) = ?core @ lp_cut_state_eval after LPIVar"
  proof -
    have mapped: "map (\<lambda>s. lp_cut_state_eval s LPIVar) (map snd steps) = u#us"
      using steps by (simp only: map_map o_def)
    have eq: "last (u#us) = lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ after) LPIVar"
      using last_mapped mapped by metis
    show ?thesis using eq by (simp only: lp_cut_state_map_def map_append)
  qed
  have bar: "lp_cut_barriers (lp_cut_state_eval bs LPIVar)" if "lp_cut_barriers bs" for bs
    using that
  proof (induct bs)
    case Nil then show ?case by (simp add: lp_cut_state_map_def)
  next
    case (Cons e es)
    have head: "lp_cut_is_barrier (lp_cut_entry_map (\<lambda>t. lp_ieval t LPIVar) e)"
      using Cons.prems by (cases e) auto
    show ?case using Cons head by (simp add: lp_cut_state_map_def)
  qed
  have core: "map (lp_cut_scope_entry r) ?core = ?core" for r
    by (simp add: lp_cut_state_map_def)
  have after: "lp_cut_barriers (lp_cut_state_eval after LPIVar)" using bar suffix by blast
  have before: "lp_cut_barriers (lp_cut_state_eval before LPIVar)" using bar suffix by blast
  show ?thesis using source.barrier_pump[OF path last after core before]
    by (simp add: lp_cut_state_map_def)
qed

definition check_source where
  "check_source q modes argv a before after initial_steps steps =
    (lp_cut_source_program P \<and> length argv=length modes \<and>
     list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
     lp_cut_barriers before \<and> lp_cut_barriers after \<and> steps \<noteq> [] \<and>
     lpp_checked_builtin_trace step_check [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] initial_steps
       ([LPCGoals [LPCAtom a]] @ before) \<and>
     lpp_checked_builtin_trace step_check [LPCGoals [LPCAtom a]] steps
       ([LPCGoals [LPCAtom a]] @ after))"

theorem check_source_sound:
  assumes checked: "check_source q modes argv a before after initial_steps steps"
  shows "length argv=length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> ground t) (zip argv modes) \<and>
    \<not> SN_on (lpp_builtin_source P U)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  have pump: "\<not> SN_on (lpp_builtin_source P U)
    {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
    by (rule trace_pump)
      (use checked in \<open>auto simp: check_source_def\<close>)
  have reach: "(lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar,
    lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar) \<in> (lpp_builtin_source P U)\<^sup>*"
    by (rule trace_sound[where steps=initial_steps])
      (use checked in \<open>simp add: check_source_def\<close>)
  have root: "\<not> SN_on (lpp_builtin_source P U)
    {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
  proof
    assume sn: "SN_on (lpp_builtin_source P U)
      {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
    have included: "{lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}
      \<subseteq> (lpp_builtin_source P U)\<^sup>* ``
        {lp_cut_state_eval [LPCGoals [LPCAtom (Fun (LPCUser q) argv)]] LPIVar}"
      using reach by auto
    have "SN_on (lpp_builtin_source P U)
      {lp_cut_state_eval ([LPCGoals [LPCAtom a]] @ before) LPIVar}"
      by (rule SN_on_subset2[OF included SN_on_Image_rtrancl[OF sn]])
    then show False using pump by contradiction
  qed
  show ?thesis using checked root
    by (simp add: check_source_def lp_cut_state_map_def)
qed

end

ML \<open>
val checked = [@{thm lpp_builtin_trace_checker.check_source_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted checked builtin trace dependency" else ();
\<close>
end
