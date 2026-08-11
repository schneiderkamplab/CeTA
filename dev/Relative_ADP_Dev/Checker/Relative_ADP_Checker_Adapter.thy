theory Relative_ADP_Checker_Adapter
  imports
    Relative_ADP_Processors_Dev.Relative_ADP_Processors
    Ord.Reduction_Pair_Implementations
    Auxx.Map_Choice
begin

type_synonym ('f, 'v) relative_adp_problem_list =
  "('f, 'v) adp list \<times> ('f, 'v) adp list"

definition erase_annotations_adp_list ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list" where
  "erase_annotations_adp_list = map erase_annotations_adp"

definition relative_adp_erasure_residual ::
  "('f, 'v) adp list \<Rightarrow> ('f, 'v) adp list \<Rightarrow>
   ('f, 'v) adp list \<Rightarrow> ('f, 'v) relative_adp_problem_list" where
  "relative_adp_erasure_residual P B selected =
    (list_diff P selected,
     list_diff B selected @ erase_annotations_adp_list selected)"

definition check_relative_adp_erasure_redpair ::
  "('f::{compare_order,showl}) redtriple_impl \<Rightarrow>
   ('f, string) adp list \<Rightarrow> ('f, string) adp list \<Rightarrow>
   ('f, string) adp list \<Rightarrow> showsl check" where
  "check_relative_adp_erasure_redpair redp P B selected = (let
      rp = get_rel_impl redp;
      strict = map erase_adp selected;
      weak = map erase_adp (P @ B)
    in do {
      check (set selected \<subseteq> set P \<union> set B)
        (showsl_lit (STR ''selected relative ADPs are not in the problem''));
      check (selected \<noteq> [])
        (showsl_lit (STR ''relative ADP reduction pair removes no ADP''));
      rel_impl_mono_redpair rp strict weak;
      rel_impl_s rp strict;
      rel_impl_ns rp weak
    })"

lemma relative_adp_erasure_residual_sets [simp]:
  "case relative_adp_erasure_residual P B selected of (P',B') \<Rightarrow>
    (set P', set B') =
      (set P - set selected,
       (set B - set selected) \<union> erase_annotations_adp ` set selected)"
  by (simp add: relative_adp_erasure_residual_def
      erase_annotations_adp_list_def)

theorem check_relative_adp_erasure_redpair_sound:
  fixes redp :: "('f::{compare_order,showl}) redtriple_impl"
  assumes checked:
      "isOK (check_relative_adp_erasure_redpair redp P B selected)"
    and residual:
      "adp_problem_SN
        (case relative_adp_erasure_residual P B selected of
          (P',B') \<Rightarrow> (set P', set B'))"
  shows "adp_problem_SN (set P, set B)"
proof -
  let ?rp = "get_rel_impl redp"
  let ?strict = "map erase_adp selected"
  let ?weak = "map erase_adp (P @ B)"
  from checked[unfolded check_relative_adp_erasure_redpair_def,
      simplified Let_def]
  have selected: "set selected \<subseteq> set P \<union> set B"
    and valid: "isOK (rel_impl_mono_redpair ?rp ?strict ?weak)"
    and strict: "isOK (rel_impl_s ?rp ?strict)"
    and weak: "isOK (rel_impl_ns ?rp ?weak)"
    by auto
  from rel_impl_mono_redpair[OF get_rel_impl valid strict weak,
      of undefined undefined]
  obtain S NS NST where order: "mono_redtriple_order S NS NST"
    and strict: "set ?strict \<subseteq> S"
    and weak: "set ?weak \<subseteq> NS"
    by auto
  have all_weak: "erase_adp ` (set P \<union> set B) \<subseteq> NS"
    using weak by auto
  have selected_strict: "erase_adp ` set selected \<subseteq> S"
    using strict by auto
  have residual': "adp_problem_SN
      (set P - set selected,
       (set B - set selected) \<union> erase_annotations_adp ` set selected)"
    using residual by (simp add: relative_adp_erasure_residual_def
        erase_annotations_adp_list_def split: prod.splits)
  show ?thesis
    by (rule relative_adp_erasure_reduction_pair[
          OF order all_weak selected_strict residual'])
qed

datatype 'f relative_adp_termination_proof =
    Relative_ADP_Empty
  | Relative_ADP_Erasure_Redpair
      "'f redtriple_impl"
      "('f adp_symbol, string) rule list"
      "'f relative_adp_termination_proof"

fun check_relative_adp_termination_proof ::
  "(('f::{compare_order,showl}) adp_symbol, string) rule list \<Rightarrow>
   ('f adp_symbol, string) rule list \<Rightarrow>
   'f relative_adp_termination_proof \<Rightarrow> showsl check" where
  "check_relative_adp_termination_proof P B Relative_ADP_Empty =
    check (P = [])
      (showsl_lit (STR ''relative ADP main component is not empty''))"
| "check_relative_adp_termination_proof P B
      (Relative_ADP_Erasure_Redpair redp selected proof) = do {
    check_relative_adp_erasure_redpair redp P B selected;
    let residual = relative_adp_erasure_residual P B selected;
    check_relative_adp_termination_proof (fst residual) (snd residual) proof
  }"

theorem check_relative_adp_termination_proof_sound:
  fixes certificate :: "('f::{compare_order,showl}) relative_adp_termination_proof"
  assumes checked:
    "isOK (check_relative_adp_termination_proof P B certificate)"
  shows "adp_problem_SN (set P, set B)"
  using checked
proof (induction certificate arbitrary: P B)
  case Relative_ADP_Empty
  then have "P = []" by simp
  then show ?case by (simp add: empty_main_adp_problem_SN)
next
  case (Relative_ADP_Erasure_Redpair redp selected continuation_certificate)
  let ?residual = "relative_adp_erasure_residual P B selected"
  from Relative_ADP_Erasure_Redpair.prems have step:
      "isOK (check_relative_adp_erasure_redpair redp P B selected)"
    and continuation:
      "isOK (check_relative_adp_termination_proof
        (fst ?residual) (snd ?residual) continuation_certificate)"
    by simp_all
  have residual_SN:
    "adp_problem_SN
      (case ?residual of (P',B') \<Rightarrow> (set P', set B'))"
    using Relative_ADP_Erasure_Redpair.IH[OF continuation]
    by (cases ?residual) simp
  show ?case
    by (rule check_relative_adp_erasure_redpair_sound[
          OF step residual_SN])
qed

end
