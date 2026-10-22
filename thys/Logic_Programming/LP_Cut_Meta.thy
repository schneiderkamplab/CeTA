theory LP_Cut_Meta
  imports LP_Cut_Source
begin

text \<open>Executable universal lowering for a known callable skeleton.
Unknown callable variables require a separate covering constructor split.
Variables in ordinary predicate arguments are not restricted.\<close>

fun lp_cut_lower_finite where
  "lp_cut_lower_finite m (Fun (LPCUser f) ts) = Some [LPCAtom (Fun (LPCUser f) ts)]"
| "lp_cut_lower_finite m (Fun LPCBang []) = Some [LPCCut m]"
| "lp_cut_lower_finite m (Fun LPCComma [a,b]) =
    (case lp_cut_lower_finite m a of None \<Rightarrow> None | Some as \<Rightarrow>
      map_option ((@) as) (lp_cut_lower_finite m b))"
| "lp_cut_lower_finite m (Fun LPCEquals [a,b]) = Some [LPCUnify a b]"
| "lp_cut_lower_finite m (Fun LPCTruth []) = Some [LPCTrue]"
| "lp_cut_lower_finite m (Fun LPCFailure []) = Some [LPCFail]"
| "lp_cut_lower_finite m (Fun LPCCallSymbol [a]) = Some [LPCMeta a]"
| "lp_cut_lower_finite m _ = None"

theorem lp_cut_lower_finite_sound:
  assumes "lp_cut_lower_finite m t = Some gs"
  shows "lp_cut_lower m (lp_ieval t \<eta>) (map (lp_cut_map (\<lambda>a. lp_ieval a \<eta>)) gs)"
  using assms
  apply (induct m t arbitrary: gs rule: lp_cut_lower_finite.induct)
  apply (auto split: option.splits intro: lp_cut_lower.intros)
  apply (blast intro: lp_cut_lower.conjunction)
  done

lemma unknown_callable_not_lowered:
  "lp_cut_lower_finite m (Fun LPCComma [Fun (LPCUser f) [],Var x]) = None"
  by simp

lemma unknown_data_is_allowed:
  "lp_cut_lower_finite m (Fun (LPCUser f) [Var x]) =
    Some [LPCAtom (Fun (LPCUser f) [Var x])]"
  by simp

lemma explicit_call_keeps_opaque_boundary:
  "lp_cut_lower_finite m (Fun LPCCallSymbol [Var x]) = Some [LPCMeta (Var x)]"
  by simp

end
