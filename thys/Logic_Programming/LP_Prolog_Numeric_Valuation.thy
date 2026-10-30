theory LP_Prolog_Numeric_Valuation
  imports LP_Prolog_Numeric_Path
begin

text \<open>A numeric child carries auxiliary coordinates in the post-state.
Choose their values independently of the recursive-call coordinates. The
pre-state is preserved, including any auxiliary values left by earlier steps.\<close>

definition lpp_binding_value where
  "lpp_binding_value bindings source_values v =
    source_values (THE x. (x,v)\<in>set bindings)"

lemma lpp_binding_value_member:
  assumes distinct: "distinct (map snd bindings)"
    and member: "(x,v)\<in>set bindings"
  shows "lpp_binding_value bindings source_values v = source_values x"
proof -
  have unique: "y=x" if "(y,v)\<in>set bindings" for y
  proof -
    have injective: "inj_on snd (set bindings)" using distinct by (simp add: distinct_map)
    have "(y,v)=(x,v)" by (rule inj_onD[OF injective _ that member]) simp
    then show ?thesis by simp
  qed
  have "(THE y. (y,v)\<in>set bindings)=x"
    by (rule the_equality[where P="\<lambda>y. (y,v)\<in>set bindings", OF member]) (rule unique)
  then show ?thesis by (simp add: lpp_binding_value_def)
qed

definition lpp_numeric_post where
  "lpp_numeric_post bindings source_values output_names output_values x =
    (if x\<in>set output_names then output_values x
     else lpp_binding_value bindings source_values (Post x))"

definition lpp_numeric_middle where
  "lpp_numeric_middle bindings source_values x =
    lpp_binding_value bindings source_values (Intermediate x)"

lemma lpp_numeric_post_output:
  "x\<in>set output_names \<Longrightarrow>
    lpp_numeric_post bindings source_values output_names output_values x = output_values x"
  by (simp add: lpp_numeric_post_def)

lemma lpp_numeric_valuation_extension:
  assumes distinct: "distinct (map snd bindings)"
    and pre: "\<And>x coordinate. (x,Pre coordinate)\<in>set bindings \<Longrightarrow> pre coordinate = source_values x"
    and fresh: "\<And>x coordinate. (x,Post coordinate)\<in>set bindings \<Longrightarrow> coordinate\<notin>set output_names"
    and member: "(x,v)\<in>set bindings"
  shows "lpp_trans_integer pre
    (lpp_numeric_post bindings source_values output_names output_values)
    (lpp_numeric_middle bindings source_values) v = source_values x"
  using lpp_binding_value_member[OF distinct member] pre fresh member
  by (cases v) (auto simp: lpp_numeric_post_def lpp_numeric_middle_def)


fun lpp_numeric_binding_admissible where
  "lpp_numeric_binding_admissible inputs outputs (x,Pre coordinate) =
    ((coordinate,Var x,LPPEVariable x)\<in>set inputs)"
| "lpp_numeric_binding_admissible inputs outputs (x,Post coordinate) =
    (coordinate\<notin>set (map fst outputs))"
| "lpp_numeric_binding_admissible inputs outputs (x,Intermediate coordinate) = True"

definition lpp_check_numeric_bindings where
  "lpp_check_numeric_bindings inputs outputs bindings =
    (distinct (map snd bindings) \<and>
      list_all (lpp_numeric_binding_admissible inputs outputs) bindings)"

theorem lpp_checked_numeric_path_witness:
  assumes checked: "lpp_check_numeric_path K inputs outputs observations numeric_tests bindings formula"
    and admissible: "lpp_check_numeric_bindings inputs outputs bindings"
    and observed: "list_all (lpp_numeric_observation_holds eta) observations"
    and known: "lpp_integer_known K eta"
    and bound_types: "\<And>x v. (x,v)\<in>set bindings \<Longrightarrow> x\<in>set K"
    and inputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set inputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (pre coordinate)"
    and outputs: "\<And>coordinate t e. (coordinate,t,e)\<in>set outputs \<Longrightarrow>
      lp_ieval t eta=lpp_integer_value (output_values coordinate)"
    and member: "Transition from to formula\<in>transition_rules system"
    and before: "IA4.satisfies (lpp_integer_assignment pre) (assertion system from)"
    and after: "\<And>post. IA4.satisfies (lpp_integer_assignment post) (assertion system to)"
  shows "\<exists>post. (State (lpp_integer_assignment pre) from,State (lpp_integer_assignment post) to)
    \<in>LPPIntegerLTS.transition system \<and>
    (\<forall>coordinate\<in>set (map fst outputs). post coordinate = output_values coordinate)"
proof -
  obtain source_values where valuation: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (source_values x)"
    using lpp_integer_known_environment[OF known] by blast
  let ?post = "lpp_numeric_post bindings source_values (map fst outputs) output_values"
  let ?middle = "lpp_numeric_middle bindings source_values"
  have distinct: "distinct (map snd bindings)"
    and admissible_rows: "list_all (lpp_numeric_binding_admissible inputs outputs) bindings"
    using admissible by (auto simp: lpp_check_numeric_bindings_def)
  have pre: "pre coordinate=source_values x" if binding: "(x,Pre coordinate)\<in>set bindings" for x coordinate
  proof -
    have input: "(coordinate,Var x,LPPEVariable x)\<in>set inputs"
      using admissible_rows binding by (auto simp: list_all_iff)
    have x: "x\<in>set K" by (rule bound_types[OF binding])
    show ?thesis using inputs[OF input] valuation[OF x] by simp
  qed
  have fresh: "coordinate\<notin>set (map fst outputs)" if "(x,Post coordinate)\<in>set bindings" for x coordinate
  proof -
    have row: "lpp_numeric_binding_admissible inputs outputs (x,Post coordinate)"
      using admissible_rows that by (auto simp only: list_all_iff)
    show ?thesis using row by simp
  qed
  have typed: "eta x=lpp_integer_value
    (lpp_trans_integer pre ?post ?middle (lpp_numeric_rename bindings x))" if x: "x\<in>set K" for x
  proof -
    have mapped: "map_of bindings x\<noteq>None"
      using checked x by (auto simp: lpp_check_numeric_path_def list_all_iff)
    obtain v where lookup: "map_of bindings x=Some v" using mapped by (cases "map_of bindings x") auto
    have binding: "(x,v)\<in>set bindings" by (rule map_of_SomeD[OF lookup])
    have renamed: "lpp_numeric_rename bindings x=v" by (simp add: lpp_numeric_rename_def lookup)
    show ?thesis using valuation[OF x] lpp_numeric_valuation_extension[OF distinct pre fresh binding]
      by (simp only: renamed)
  qed
  have output_rep: "lp_ieval t eta=lpp_integer_value (?post coordinate)"
    if row: "(coordinate,t,e)\<in>set outputs" for coordinate t e
    using outputs[OF row] row by (auto simp: lpp_numeric_post_def image_iff Bex_def)
  have edge: "(State (lpp_integer_assignment pre) from,State (lpp_integer_assignment ?post) to)
    \<in>LPPIntegerLTS.transition system"
    by (rule lpp_checked_numeric_path_step[where eta=eta and middle="?middle",
      OF checked observed typed inputs output_rep member before after])
  show ?thesis by (rule exI[of _ ?post])
    (use edge in \<open>simp add: lpp_numeric_post_def\<close>)
qed

ML \<open>
val checked = [@{thm lpp_numeric_valuation_extension}, @{thm lpp_checked_numeric_path_witness}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric valuation dependency" else ();
\<close>
end
