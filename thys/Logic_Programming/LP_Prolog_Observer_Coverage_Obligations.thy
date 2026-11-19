theory LP_Prolog_Observer_Coverage_Obligations
 imports LP_Prolog_Observer_Internal_Coverage
begin

datatype lpp_observer_coverage_obligation =
 LPPODimensions | LPPOEquality nat | LPPOUniv nat

definition lpp_observer_coverage_obligations where
 "lpp_observer_coverage_obligations T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses =
  (if length states=length nds \<and> length contexts=length nds \<and> length Fs=length nds \<and>
      length functors=length nds \<and> length separation_contexts=length nds \<and>
      length actions=length nds \<and> length witnesses=length nds
   then concat (map (\<lambda>i.
    (if lpp_observer_equality_frame (states!i) \<and>
        \<not>lpp_check_observer_equality_row T fuel P Q nds states contexts Fs functors separation_contexts i (actions!i) (witnesses!i)
     then [LPPOEquality i] else []) @
    (if lpp_observer_may_univ (states!i) \<and>
        \<not>lpp_check_observer_univ_row T fuel P Q nds states contexts Fs functors separation_contexts returned arity i (actions!i) (witnesses!i)
     then [LPPOUniv i] else [])) [0..<length nds])
   else [LPPODimensions])"

lemma lpp_observer_coverage_obligations_complete:
 "lpp_observer_coverage_obligations T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses = [] \<longleftrightarrow>
  lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 by (auto simp: lpp_observer_coverage_obligations_def lpp_check_observer_internal_coverage_def
   list_all_iff split: if_splits)

lemma lpp_observer_coverage_obligations_reject_pending:
 "obligation \<in> set (lpp_observer_coverage_obligations T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses) \<Longrightarrow>
  \<not>lpp_check_observer_internal_coverage T fuel P Q nds states contexts Fs functors separation_contexts returned arity actions witnesses"
 by (metis lpp_observer_coverage_obligations_complete empty_iff list.set(1))

ML \<open>
val thms = @{thms lpp_observer_coverage_obligations_complete lpp_observer_coverage_obligations_reject_pending};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted observer coverage obligations" else ();
\<close>
end
