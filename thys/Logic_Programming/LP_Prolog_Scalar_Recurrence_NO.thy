theory LP_Prolog_Scalar_Recurrence_NO
 imports LP_Prolog_Scalar_Recurrence_Check
begin

fun lpp_scalar_initial_argument where
 "lpp_scalar_initial_argument None = lpp_integer_term 0"
| "lpp_scalar_initial_argument (Some w) = lpp_machine_term w"

lemma lpp_scalar_initial_ground:
 "ground (lpp_scalar_initial_argument observation)"
proof (cases observation)
 case None show ?thesis by (simp add: None lpp_integer_term_def ground_vars_term_empty)
next
 case (Some w) show ?thesis by (cases w) (simp_all add: Some lpp_integer_term_def ground_vars_term_empty)
qed

lemma lpp_scalar_initial_observations:
 assumes valid: "list_all (\<lambda>v. case v of None \<Rightarrow> True | Some w \<Rightarrow> lpp_machine_valid w) observations"
 shows "lpp_scalar_observations (lpp_binary64_profile_operation fallback) observations
   (map (\<lambda>v. lp_ieval (lpp_scalar_initial_argument v) LPIVar) observations)"
proof -
 have each: "lpp_stable_scalar_evaluation (lpp_binary64_profile_operation fallback)
     (lp_ieval (lpp_scalar_initial_argument (observations!i)) LPIVar) (lpp_machine_value w)"
   if bound: "i<length observations" and entry: "observations!i=Some w" for i w
 proof -
  have raw: "case observations!i of None \<Rightarrow> True | Some v \<Rightarrow> lpp_machine_valid v"
    using valid nth_mem[OF bound] by (simp add: list_all_iff)
  have scalar: "lpp_machine_valid w" using raw entry by simp
  show ?thesis by (simp only: entry lpp_scalar_initial_argument.simps lpp_machine_term_eval;
    rule lpp_stable_scalar_evaluation.scalar[OF lpp_machine_scalar_fraction[OF scalar]])
 qed
 show ?thesis using each
   by (auto simp: lpp_scalar_observations_def list_all_iff split: option.splits)
qed

definition lpp_check_scalar_recurrence where
 "lpp_check_scalar_recurrence P q modes observations selection H actions outputs recipes failures =
   (length modes=length observations \<and> lp_cut_source_program P \<and>
    list_all (\<lambda>v. case v of None \<Rightarrow> True | Some w \<Rightarrow> lpp_machine_valid w) observations \<and>
    lpp_scalar_recurrence_check P q observations selection H actions outputs recipes failures)"

theorem lpp_check_scalar_recurrence_sound:
 assumes checked: "lpp_check_scalar_recurrence P q modes observations selection H actions outputs recipes failures"
 shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
   \<not>SN_on (lpp_builtin_source P (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
     {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
 let ?operation = "lpp_binary64_profile_operation fallback"
 let ?R = "lpp_builtin_source P (lpp_stable_source_builtin ?operation)"
 let ?argv = "map lpp_scalar_initial_argument observations"
 let ?initial = "[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ?argv))]]"
 let ?states = "{s. \<exists>actuals gs es. s=LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es \<and>
     lpp_scalar_observations ?operation observations actuals}"
 have recurrence: "lpp_scalar_recurrence_check P q observations selection H actions outputs recipes failures"
   and valid: "list_all (\<lambda>v. case v of None \<Rightarrow> True | Some w \<Rightarrow> lpp_machine_valid w) observations"
   using checked by (auto simp: lpp_check_scalar_recurrence_def)
 have initial_observed: "lpp_scalar_observations ?operation observations (map (\<lambda>t. lp_ieval t LPIVar) ?argv)"
   using lpp_scalar_initial_observations[OF valid, where fallback=fallback] by (simp add: map_map o_def)
 have start: "?initial\<in>?states" using initial_observed by blast
 have successors: "\<exists>v\<in>?states. (s,v)\<in>?R\<^sup>+" if member: "s\<in>?states" for s
 proof -
  obtain actuals gs es where shape: "s=LPCGoals (LPCAtom (LPIFun (LPCUser q) actuals)#gs)#es"
    and observed: "lpp_scalar_observations ?operation observations actuals" using member by blast
  obtain next_args pending saved where next_observed: "lpp_scalar_observations ?operation observations next_args"
    and step: "(s,LPCGoals (LPCAtom (LPIFun (LPCUser q) next_args)#pending)#saved)\<in>?R\<^sup>+"
    using lpp_scalar_recurrence_progress[OF recurrence observed, where gs=gs and es=es] shape by blast
  show ?thesis using next_observed step by blast
 qed
 have no: "\<not>SN_on ?R {?initial}"
   by (rule lp_source_recurrent_simulation[where X="{()}" and a="()" and S="{((),())}"
       and rep="\<lambda>_ s. s\<in>?states"])
      (use start successors in auto)
 have lengths: "length ?argv=length modes" using checked by (simp add: lpp_check_scalar_recurrence_def)
 have ground: "list_all ground ?argv" by (auto simp: list_all_iff intro: lpp_scalar_initial_ground)
 show ?thesis by (rule exI[of _ "?argv"]) (use lengths ground no in blast)
qed

ML \<open>
val checked = [@{thm lpp_check_scalar_recurrence_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted scalar-expression source nontermination dependency" else ();
\<close>
end
