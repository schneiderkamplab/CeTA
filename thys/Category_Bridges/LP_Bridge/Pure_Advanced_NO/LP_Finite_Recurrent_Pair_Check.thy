theory LP_Finite_Recurrent_Pair_Check
  imports LP_Finite_Recurrent_Pair
begin

theorem lp_finite_recurrent_pair_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_recurrent_pair_check P q arity positions A C x y s d n m a b c keep steps1 steps2"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ld P) {[(q,map (\<lambda>t. lp_finite_eval t Var) ts)]}"
proof -
  let ?initial = "lp_rec_fill A x y s (lp_rec_power C x m s)"
  obtain h1 b1 h2 b2 where shapes:
    "lp_rec_templates A C x y s d n m a b c keep=(h1,b1,h2,b2)"
    by (cases "lp_rec_templates A C x y s d n m a b c keep") auto
  have xy: "x\<noteq>y" and av: "\<Union>(vars_term ` set (snd A))\<subseteq>{x,y}"
    and cv: "vars_term C\<subseteq>{x}" and sg: "ground s" and bound: "n\<le>m"
    and query: "fst ?initial=q" "length (snd ?initial)=arity"
      "\<forall>i\<in>set positions. i<arity \<and> ground (snd ?initial!i)"
    and progress: "steps1\<noteq>[]" "steps2\<noteq>[]"
    using ok unfolding lp_recurrent_pair_check_def
    by (auto simp: Let_def shapes list_all_iff)
  obtain bs1 bs2 where run1: "lp_match_run P [h1] steps1=Some (b1#bs1)"
    and run2: "lp_match_run P [h2] steps2=Some (b2#bs2)"
    using ok unfolding lp_recurrent_pair_check_def
    by (auto simp: Let_def shapes split: option.splits list.splits)
  have bad: "\<not>SN_on (lp_ld P) {[lp_finite_atom_eval ?initial Var]}"
    by (rule lp_finite_recurrent_pair_sound[OF xy av cv sg bound shapes run1 run2 progress])
  show ?thesis by (rule exI[of _ "snd ?initial"])
    (use query bad in \<open>auto simp: lp_atom_subst_def\<close>)
qed


end
