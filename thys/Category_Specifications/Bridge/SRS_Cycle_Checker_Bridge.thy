theory SRS_Cycle_Checker_Bridge
  imports SRS_Cycle_Equivalence Cycle_Checker.Cycle_Morphism
begin
text \<open>The existing cycle checker exposes nontermination criteria. Each
acceptance below entails the negation of the same canonical cycle property.
There is no certificate-assumption mechanism in these Boolean checks.\<close>
corollary srs_cycle_transport_checker_NO:
  "check_cycle_transport R w ss u v p s ext right \<Longrightarrow> \<not> srs_cycle_terminates (set R)"
  using check_cycle_transport_sound by (simp add: srs_cycle_terminates_iff)
corollary srs_cycle_embedding_checker_NO:
  "check_cycle_embedding R w ss left right \<Longrightarrow> \<not> srs_cycle_terminates (set R)"
  using check_cycle_embedding_sound by (simp add: srs_cycle_terminates_iff)
corollary srs_cycle_morphism_checker_NO:
  "check_cycle_morphism_direction R pivot A F T B mirrored \<Longrightarrow> \<not> srs_cycle_terminates (set R)"
  using check_cycle_morphism_direction_sound by (simp add: srs_cycle_terminates_iff)
ML \<open>
  val _ = if Thm_Deps.has_skip_proof @{thms cycle_string_step_iff
    srs_cycle_terminates_iff srs_cycle_transport_checker_NO
    srs_cycle_embedding_checker_NO srs_cycle_morphism_checker_NO}
    then error "SRS Cycle: admitted proof in dependencies" else ()
\<close>
end
