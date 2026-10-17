theory Relative_ADP_Carrier
  imports Relative_ADP_Multihole_Dev.Relative_ADP_Multihole
begin

text \<open>
  Each hole retained by the evolving context belongs to one of the immediate
  arguments of the initial minimal term.  Its location records the represented
  subterm in that argument's current carrier.  Locations belonging to the same
  carrier are pairwise parallel, as required in the construction in Theorem 23.
\<close>

definition carrier_cover ::
  "('f, 'v) term list \<Rightarrow> nat list \<Rightarrow> pos list \<Rightarrow>
    ('f, 'v) term list \<Rightarrow> bool" where
  "carrier_cover holes owners locations carriers \<longleftrightarrow>
    length owners = length holes \<and>
    length locations = length holes \<and>
    (\<forall>i < length holes.
      owners ! i < length carriers \<and>
      locations ! i \<in> poss (carriers ! (owners ! i)) \<and>
      holes ! i = carriers ! (owners ! i) |_ (locations ! i)) \<and>
    (\<forall>i < length holes. \<forall>j < length holes.
      i \<noteq> j \<longrightarrow> owners ! i = owners ! j \<longrightarrow>
      (locations ! i) \<bottom> (locations ! j))"

definition initial_carrier_owners :: "'a list \<Rightarrow> nat list" where
  "initial_carrier_owners xs = [0..<length xs]"

definition initial_carrier_locations :: "'a list \<Rightarrow> pos list" where
  "initial_carrier_locations xs = replicate (length xs) []"

lemma initial_carrier_cover:
  "carrier_cover xs (initial_carrier_owners xs)
    (initial_carrier_locations xs) xs"
  unfolding carrier_cover_def initial_carrier_owners_def
    initial_carrier_locations_def
  by (auto simp: nth_replicate)

lemma initial_root_carrier_decomposition:
  assumes "is_Fun t"
  shows
    "fill_holes (root_hole_mctxt t) (root_hole_terms t) = t"
    "num_holes (root_hole_mctxt t) = length (root_hole_terms t)"
    "poss_mctxt (root_hole_mctxt t) = {[]}"
    "carrier_cover (root_hole_terms t)
      (initial_carrier_owners (root_hole_terms t))
      (initial_carrier_locations (root_hole_terms t))
      (root_hole_terms t)"
  using assms root_hole_fill root_hole_num_holes
    root_hole_context_positions initial_carrier_cover by blast+

lemma carrier_coverD:
  assumes "carrier_cover holes owners locations carriers"
    and "i < length holes"
  shows
    "length owners = length holes"
    "length locations = length holes"
    "owners ! i < length carriers"
    "locations ! i \<in> poss (carriers ! (owners ! i))"
    "holes ! i = carriers ! (owners ! i) |_ (locations ! i)"
  using assms unfolding carrier_cover_def by blast+

lemma carrier_cover_parallelD:
  assumes cover: "carrier_cover holes owners locations carriers"
    and i: "i < length holes" and j: "j < length holes"
    and distinct: "i \<noteq> j" and owner: "owners ! i = owners ! j"
  shows "(locations ! i) \<bottom> (locations ! j)"
  using assms unfolding carrier_cover_def by blast

end
