theory Outermost_RZ_Checker
  imports
    Outermost_Signature_Extension
    Proof_Checker_Base.Check_Termination
begin

definition rz_quasi_left_linear_check where
  "rz_quasi_left_linear_check R =
    list_all (\<lambda>l. list_ex (\<lambda>k. linear_term k \<and> matches l k)
      (map fst R)) (map fst R)"

lemma rz_quasi_left_linear_check_sound:
  assumes "rz_quasi_left_linear_check R"
  shows "quasi_left_linear_lhss (fst ` set R)"
  using assms
  unfolding rz_quasi_left_linear_check_def quasi_left_linear_lhss_def
    list_all_iff list_ex_iff matches_iff
  by auto

definition rz_pattern_check where
  "rz_pattern_check F patterns = list_all (\<lambda>s.
    is_Fun s \<and> linear_term s \<and> set (funas_term_list s) \<subseteq> set F)
    patterns"

lemma rz_pattern_check_sound:
  assumes "rz_pattern_check F patterns" and "s \<in> set patterns"
  shows "is_Fun s" "linear_term s" "funas_term s \<subseteq> set F"
  using assms unfolding rz_pattern_check_def list_all_iff by auto

definition rz_flat_keys where
  "rz_flat_keys F = map fst (filter (\<lambda>fn. snd fn > 0) F)"

definition rz_flat_map_check where
  "rz_flat_map_check F flats =
    (distinct (map fst flats) \<and> set (map fst flats) = set (rz_flat_keys F))"

definition rz_flat_of where
  "rz_flat_of flats fn = the (map_of flats (fst fn))"

definition rz_generated_rules where
  "rz_generated_rules top_sym up_sym down block c flats R patterns =
    (let F0 = remdups (funas_trs_list R);
         F1 = remdups ((c,0) # F0)
     in rz_transformed_rules_list top_sym up_sym down block (rz_flat_of flats)
          ''__rz_reset'' F1 R patterns)"

datatype ('f, 'l, 'v) outermost_rz_termination_proof =
  Outermost_RZ_Transformation
    "('f, 'l) lab"
    "('f, 'l) lab"
    "('f, 'l) lab"
    "('f, 'l) lab"
    "('f, 'l) lab"
    "((('f, 'l) lab) \<times> ('f, 'l) lab) list"
    "(('f, 'l) lab, 'v) term list"
    "('f, 'l, 'v) trs_termination_proof"

fun check_outermost_rz_termination_proof ::
  "('tp, ('f::{showl,compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
   ('dpp, ('f,label_type) lab, string) dpp_ops \<Rightarrow>
   showsl \<Rightarrow> ('f,label_type,string) trsLL \<Rightarrow>
   ('f,label_type,string) outermost_rz_termination_proof \<Rightarrow> showsl check"
where
  "check_outermost_rz_termination_proof I J i R
      (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child) =
    debug i (STR ''Raffelsieper-Zantema outermost transformation'') (do {
      check_wf_trs R;
      let F0 = remdups (funas_trs_list R);
      let F1 = remdups ((c,0) # F0);
      check (rz_quasi_left_linear_check R)
        (showsl_lit (STR ''left-hand sides are not quasi-left-linear''));
      check ((c,0) \<notin> set F0)
        (showsl_lit (STR ''grounding constant is not fresh''));
      check ((block,0) \<notin> set F1)
        (showsl_lit (STR ''tree-automata marker is not fresh''));
      check (rz_flat_map_check F1 flats)
        (showsl_lit (STR ''flat-symbol map does not cover the positive-arity signature exactly''));
      check (rz_pattern_check F1 patterns)
        (showsl_lit (STR ''non-redex patterns are malformed''));
      check (rz_cover_check F1 block ''__rz_cover''
        (rz_linear_lhss R @ patterns))
        (showsl_lit (STR ''non-redex patterns do not cover the source signature''));
      let generated = rz_generated_rules top_sym up_sym down block c flats R patterns;
      check_trs_termination_proof I J False (add_index i 1)
        (tp_ops.mk I False [] generated []) child
    })"

lemma check_outermost_rz_termination_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_outermost_rz_termination_proof I J i R p)"
  shows "SN (ostep (fst ` set R) (set R))"
proof (cases p)
  case (Outermost_RZ_Transformation top_sym up_sym down block c flats patterns child)
  let ?F0 = "remdups (funas_trs_list R)"
  let ?F1 = "remdups ((c,0) # ?F0)"
  let ?generated = "rz_generated_rules top_sym up_sym down block c flats R patterns"
  from ok Outermost_RZ_Transformation have wf: "wf_trs (set R)"
    and quasi_check: "rz_quasi_left_linear_check R"
    and fresh: "(c,0) \<notin> set ?F0"
    and marker: "(block,0) \<notin> set ?F1"
    and flat: "rz_flat_map_check ?F1 flats"
    and patterns: "rz_pattern_check ?F1 patterns"
    and cover: "rz_cover_check ?F1 block ''__rz_cover''
      (rz_linear_lhss R @ patterns)"
    and child_ok: "isOK (check_trs_termination_proof I J False (add_index i 1)
      (tp_ops.mk I False [] ?generated []) child)"
    by (auto simp: Let_def)
  from check_trs_termination_proof[OF I J child_ok]
  have generated_SN: "SN (rstep (set ?generated))"
    unfolding tp_spec.mk_sound[OF I] SN_qrel_def by auto
  have quasi: "quasi_left_linear_lhss (fst ` set R)"
    by (rule rz_quasi_left_linear_check_sound[OF quasi_check])
  have source_sig: "funas_trs (set R) \<subseteq> set ?F0" by simp
  have signature: "set ?F1 = insert (c,0) (set ?F0)" by auto
  have fresh_source: "(c,0) \<notin> funas_trs (set R)"
    using fresh by simp
  have pattern_fun: "s \<in> set patterns \<Longrightarrow> is_Fun s" for s
    using rz_pattern_check_sound(1)[OF patterns] .
  have pattern_linear: "s \<in> set patterns \<Longrightarrow> linear_term s" for s
    using rz_pattern_check_sound(2)[OF patterns] .
  have pattern_sig: "s \<in> set patterns \<Longrightarrow>
      funas_term s \<subseteq> set ?F1" for s
    using rz_pattern_check_sound(3)[OF patterns] .
  have transformed: "set (rz_transformed_rules_list top_sym up_sym down block
      (rz_flat_of flats) ''__rz_reset'' ?F1 R patterns) \<subseteq>
      set ?generated"
    unfolding rz_generated_rules_def Let_def by simp
  have source_SN: "SN (sig_step (set ?F0)
      (ostep (fst ` set R) (set R)))"
    by (rule rz_cover_check_transformed_rules_list_sound[
      OF quasi source_sig signature fresh_source marker pattern_fun pattern_linear
        pattern_sig cover transformed generated_SN])
  interpret C: cleaning_same_var "set ?F0" "\<lambda>_. Var ''__rz_clean''"
      "Var ''__rz_clean''"
    by unfold_locales auto
  show ?thesis
    by (rule C.SN_sig_ostep_imp_SN_ostep[OF wf source_sig quasi source_SN])
qed

lemmas check_outermost_rz_termination_proof_global_sound =
  check_outermost_rz_termination_proof_sound

end
