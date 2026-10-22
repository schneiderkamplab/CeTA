theory LP_Recurrent_Pair_Check
  imports LP_Recurrent_Pair
begin

text \<open>The certificate supplies contexts and two source traces, not an
  assertion that either phase is a valid transition. Both traces are replayed
  against the complete source clauses. The initial query is constructed from
  the ground seed and checked against the requested mode.\<close>

definition lp_recurrent_pair_check where
  "lp_recurrent_pair_check P q arity positions A C x y s d n m a b c keep steps1 steps2 =
    (let initial=lp_rec_fill A x y s (lp_rec_power C x m s);
         (h1,b1,h2,b2)=lp_rec_templates A C x y s d n m a b c keep
     in x\<noteq>y \<and> \<Union>(vars_term ` set (snd A))\<subseteq>{x,y} \<and>
       vars_term C\<subseteq>{x} \<and> ground s \<and> n\<le>m \<and>
       fst initial=q \<and> length (snd initial)=arity \<and>
       list_all (\<lambda>i. i<arity \<and> ground (snd initial!i)) positions \<and>
       steps1\<noteq>[] \<and> steps2\<noteq>[] \<and>
       (case lp_match_run P [h1] steps1 of Some (v#vs) \<Rightarrow> v=b1 | _ \<Rightarrow> False) \<and>
       (case lp_match_run P [h2] steps2 of Some (v#vs) \<Rightarrow> v=b2 | _ \<Rightarrow> False))"

theorem lp_recurrent_pair_check_sound:
  fixes P :: "('f,'v) lp_clause list"
  assumes ok: "lp_recurrent_pair_check P q arity positions A C x y s d n m a b c keep steps1 steps2"
  shows "\<exists>ts :: ('f,'v) term list. length ts=arity \<and>
    (\<forall>i\<in>set positions. i<arity \<and> ground (ts!i)) \<and>
    \<not>SN_on (lp_ild P) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ts)]}"
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
  have bad: "\<not>SN_on (lp_ild P) {[lp_atom_eval ?initial LPIVar]}"
    by (rule lp_recurrent_pair_sound[OF xy av cv sg bound shapes run1 run2 progress])
  show ?thesis by (rule exI[of _ "snd ?initial"])
    (use query bad in \<open>simp add: lp_atom_eval_def\<close>)
qed

end
