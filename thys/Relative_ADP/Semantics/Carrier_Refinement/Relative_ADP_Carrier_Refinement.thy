theory Relative_ADP_Carrier_Refinement
  imports Relative_ADP_Root_Base_State_Dev.Relative_ADP_Root_Base_State
begin

definition carrier_refinement ::
  "('f, 'v) term list \<Rightarrow> nat list \<Rightarrow> pos list \<Rightarrow>
    ('f, 'v) term list \<Rightarrow> bool" where
  "carrier_refinement new_holes parents tails old_holes \<longleftrightarrow>
    length parents = length new_holes \<and>
    length tails = length new_holes \<and>
    (\<forall>i < length new_holes.
      parents ! i < length old_holes \<and>
      tails ! i \<in> poss (old_holes ! (parents ! i)) \<and>
      new_holes ! i = old_holes ! (parents ! i) |_ (tails ! i)) \<and>
    (\<forall>i < length new_holes. \<forall>j < length new_holes.
      i \<noteq> j \<longrightarrow> parents ! i = parents ! j \<longrightarrow>
      (tails ! i) \<bottom> (tails ! j))"

definition refined_carrier_owners :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "refined_carrier_owners owners parents = map ((!) owners) parents"

definition refined_carrier_locations ::
  "pos list \<Rightarrow> nat list \<Rightarrow> pos list \<Rightarrow> pos list" where
  "refined_carrier_locations locations parents tails =
    map (\<lambda>i. locations ! (parents ! i) @ tails ! i)
      [0..<length parents]"

lemma parallel_pos_append_both:
  fixes p q a b :: pos
  assumes "p \<bottom> q"
  shows "p @ a \<bottom> q @ b"
proof -
  have "p \<bottom> q @ b" by (rule parallel_pos_append_right[OF assms])
  then have "q @ b \<bottom> p" by (rule parallel_pos_sym)
  then have "q @ b \<bottom> p @ a" by (rule parallel_pos_append_right)
  then show ?thesis by (rule parallel_pos_sym)
qed

lemma parallel_pos_append_common_left:
  fixes p a b :: pos
  assumes "a \<bottom> b"
  shows "p @ a \<bottom> p @ b"
  using assms by (induct p) auto

lemma carrier_cover_refinement:
  assumes cover: "carrier_cover old_holes owners locations carriers"
    and refinement: "carrier_refinement new_holes parents tails old_holes"
  shows "carrier_cover new_holes
    (refined_carrier_owners owners parents)
    (refined_carrier_locations locations parents tails) carriers"
proof -
  from refinement have parent_length: "length parents = length new_holes"
    and tail_length: "length tails = length new_holes"
    and refined:
      "\<And>i. i < length new_holes \<Longrightarrow>
        parents ! i < length old_holes \<and>
        tails ! i \<in> poss (old_holes ! (parents ! i)) \<and>
        new_holes ! i = old_holes ! (parents ! i) |_ (tails ! i)"
    and same_parent:
      "\<And>i j. i < length new_holes \<Longrightarrow>
        j < length new_holes \<Longrightarrow> i \<noteq> j \<Longrightarrow>
        parents ! i = parents ! j \<Longrightarrow>
        tails ! i \<bottom> tails ! j"
    unfolding carrier_refinement_def by blast+
  have owner_length:
    "length (refined_carrier_owners owners parents) = length new_holes"
    unfolding refined_carrier_owners_def using parent_length by simp
  have location_length:
    "length (refined_carrier_locations locations parents tails) =
      length new_holes"
    unfolding refined_carrier_locations_def using parent_length by simp
  have point:
    "refined_carrier_owners owners parents ! i < length carriers \<and>
     refined_carrier_locations locations parents tails ! i
       \<in> poss (carriers ! (refined_carrier_owners owners parents ! i)) \<and>
     new_holes ! i =
       carriers ! (refined_carrier_owners owners parents ! i) |_
         (refined_carrier_locations locations parents tails ! i)"
    if i: "i < length new_holes" for i
  proof -
    let ?j = "parents ! i"
    from refined[OF i] have j: "?j < length old_holes"
      and tail: "tails ! i \<in> poss (old_holes ! ?j)"
      and new: "new_holes ! i = old_holes ! ?j |_ (tails ! i)"
      by blast+
    from carrier_coverD[OF cover j] have owner: "owners ! ?j < length carriers"
      and location: "locations ! ?j \<in> poss (carriers ! (owners ! ?j))"
      and old: "old_holes ! ?j = carriers ! (owners ! ?j) |_ (locations ! ?j)"
      by blast+
    have combined:
      "locations ! ?j @ tails ! i \<in> poss (carriers ! (owners ! ?j))"
      using location tail old by (simp only: poss_append_poss)
    have at:
      "new_holes ! i = carriers ! (owners ! ?j) |_
        (locations ! ?j @ tails ! i)"
      using new old subt_at_append[OF location, of "tails ! i"] by simp
    show ?thesis
      unfolding refined_carrier_owners_def refined_carrier_locations_def
      using i parent_length owner combined at by simp
  qed
  have parallel:
    "refined_carrier_locations locations parents tails ! i \<bottom>
      refined_carrier_locations locations parents tails ! j"
    if i: "i < length new_holes" and j: "j < length new_holes"
      and distinct: "i \<noteq> j"
      and owner_eq:
        "refined_carrier_owners owners parents ! i =
          refined_carrier_owners owners parents ! j"
    for i j
  proof -
    let ?pi = "parents ! i"
    let ?pj = "parents ! j"
    from refined[OF i] refined[OF j] have pi: "?pi < length old_holes"
      and pj: "?pj < length old_holes" by blast+
    have owners_eq: "owners ! ?pi = owners ! ?pj"
      using owner_eq i j parent_length
      unfolding refined_carrier_owners_def by simp
    have locations_parallel:
      "locations ! ?pi @ tails ! i \<bottom>
        locations ! ?pj @ tails ! j"
    proof (cases "?pi = ?pj")
      case True
      have "tails ! i \<bottom> tails ! j"
        by (rule same_parent[OF i j distinct True])
      then show ?thesis unfolding True
        by (rule parallel_pos_append_common_left)
    next
      case False
      have "locations ! ?pi \<bottom> locations ! ?pj"
        by (rule carrier_cover_parallelD[OF cover pi pj False owners_eq])
      then show ?thesis by (rule parallel_pos_append_both)
    qed
    show ?thesis
      unfolding refined_carrier_locations_def
      using i j parent_length locations_parallel by simp
  qed
  show ?thesis
    unfolding carrier_cover_def
    using owner_length location_length point parallel by blast
qed

end
