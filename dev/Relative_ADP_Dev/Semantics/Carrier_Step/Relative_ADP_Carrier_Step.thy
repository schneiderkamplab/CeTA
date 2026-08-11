theory Relative_ADP_Carrier_Step
  imports Relative_ADP_Construction_State_Dev.Relative_ADP_Construction_State
begin

lemma carrier_replace_at_append:
  assumes p: "p \<in> poss t"
    and q: "q \<in> poss (t |_ p)"
  shows "replace_at t (p @ q) u =
    replace_at t p (replace_at (t |_ p) q u)"
  unfolding ctxt_of_pos_term_append[OF p]
  by (simp add: replace_at_subt_at[OF p])

lemma carrier_cover_inner_update:
  fixes u :: "('f, 'v) term"
    and owner :: nat
    and location :: pos
  assumes cover: "carrier_cover holes owners locations carriers"
    and i: "i < length holes"
    and beta: "beta \<in> poss (holes ! i)"
  defines "owner \<equiv> owners ! i"
    and "location \<equiv> locations ! i"
    and "hole' \<equiv> replace_at (holes ! i) beta u"
    and "carrier' \<equiv>
      replace_at (carriers ! owner) (location @ beta) u"
  shows "carrier_cover (holes[i := hole']) owners locations
    (carriers[owner := carrier'])"
proof -
  from carrier_coverD[OF cover i] have owner: "owner < length carriers"
    and location: "location \<in> poss (carriers ! owner)"
    and hole: "holes ! i = carriers ! owner |_ location"
    unfolding owner_def location_def by blast+
  have beta_carrier: "beta \<in> poss (carriers ! owner |_ location)"
    using beta hole by simp
  have redex_pos: "location @ beta \<in> poss (carriers ! owner)"
    using location beta_carrier by (simp only: poss_append_poss)
  have location_after: "location \<in> poss carrier'"
    unfolding carrier'_def
    by (rule replace_at_below_poss[OF redex_pos]) auto
  have at_location:
    "carrier' |_ location = hole'"
  proof -
    have nested: "carrier' = replace_at (carriers ! owner) location
      (replace_at (carriers ! owner |_ location) beta u)"
      unfolding carrier'_def
      by (rule carrier_replace_at_append[OF location beta_carrier])
    show ?thesis
      unfolding nested hole'_def hole
      by (simp add: replace_at_subt_at[OF location])
  qed
  from cover have owner_length: "length owners = length holes"
    and location_length: "length locations = length holes"
    unfolding carrier_cover_def by blast+
  have point:
    "owners ! j < length (carriers[owner := carrier']) \<and>
     locations ! j \<in> poss ((carriers[owner := carrier']) ! (owners ! j)) \<and>
     (holes[i := hole']) ! j =
       (carriers[owner := carrier']) ! (owners ! j) |_ locations ! j"
    if j: "j < length holes" for j
  proof (cases "j = i")
    case True
    show ?thesis
      unfolding True owner_def[symmetric] location_def[symmetric]
      using i owner location_after at_location by simp
  next
    case False
    from carrier_coverD[OF cover j] have j_owner: "owners ! j < length carriers"
      and j_location: "locations ! j \<in> poss (carriers ! (owners ! j))"
      and j_hole: "holes ! j =
        carriers ! (owners ! j) |_ locations ! j" by blast+
    show ?thesis
    proof (cases "owners ! j = owner")
      case owner_eq: True
      have locations_parallel: "locations ! j \<bottom> location"
        unfolding location_def
        by (rule carrier_cover_parallelD[OF cover j i False])
           (use owner_eq owner_def in simp)
      have rewrite_parallel: "locations ! j \<bottom> location @ beta"
        by (rule parallel_pos_append_right[OF locations_parallel])
      have j_location_owner: "locations ! j \<in> poss (carriers ! owner)"
        using j_location owner_eq by simp
      have j_location_after: "locations ! j \<in> poss carrier'"
        unfolding carrier'_def
        using parallel_poss_replace_at[
          OF parallel_pos_sym[OF rewrite_parallel] redex_pos]
          j_location_owner by simp
      have j_at_after: "carrier' |_ locations ! j = holes ! j"
        unfolding carrier'_def
        using parallel_replace_at_subt_at[
          OF parallel_pos_sym[OF rewrite_parallel] redex_pos j_location_owner]
          j_hole owner_eq by simp
      show ?thesis using False owner owner_eq j_location_after j_at_after by simp
    next
      case owner_neq: False
      show ?thesis using False owner_neq j_owner j_location j_hole by simp
    qed
  qed
  show ?thesis
    unfolding carrier_cover_def
    using owner_length location_length point cover
    by (auto simp: carrier_cover_def)
qed

end
