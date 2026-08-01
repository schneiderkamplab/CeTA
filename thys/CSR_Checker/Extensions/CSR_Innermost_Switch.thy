(*
Author:  Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Innermost_Switch
  imports
    CSR_Minimal_CSDP_Proofs
    CR.Orthogonality_Impl
begin

text \<open>
  Executable applicability test for the Giesl--Middeldorp switch from
  termination to innermost termination of context-sensitive rewriting.

  Root overlaps are harmless only when their critical pair is trivial.  A
  proper overlap is rejected even if its critical pair happens to be trivial:
  the proof of the switch needs the non-overlap property for proper subterms of
  left-hand sides.  Left-linearity is checked separately; Example 10 of
  Giesl--Middeldorp shows that non-overlap alone is insufficient.
\<close>

definition check_csr_orthogonal ::
  "('f::{showl,compare_order},string) rules
    \<Rightarrow> showsl check"
where
  "check_csr_orthogonal R = do {
    check_left_linear_trs R
      <+? (\<lambda>s. showsl_lit
        (STR ''the CSR is not left-linear\<newline>'') \<circ> s);
    check_allm (\<lambda>(at_root,s,t).
      check (at_root \<and> s = t)
        (showsl_lit
          (STR ''the CSR has a non-root or non-trivial overlap: '') \<circ>
         showsl s \<circ> showsl_lit (STR '' <- . -> '') \<circ> showsl t))
      (critical_pairs_impl string_rename R R)
  }"

lemma check_csr_orthogonal_left_linear:
  assumes "isOK (check_csr_orthogonal R)"
  shows "left_linear_trs (set R)"
  using assms unfolding check_csr_orthogonal_def by auto

lemma check_csr_orthogonal_critical_pairs:
  assumes ok: "isOK (check_csr_orthogonal R)"
    and cp: "(at_root,s,t) \<in>
      critical_pairs string_rename (set R) (set R)"
  shows "at_root \<and> s = t"
proof -
  from cp have mem:
    "(at_root,s,t) \<in> set (critical_pairs_impl string_rename R R)"
    by simp
  from ok mem show ?thesis
    unfolding check_csr_orthogonal_def by auto
qed

lemma check_csr_orthogonal_no_proper_overlap:
  assumes ok: "isOK (check_csr_orthogonal R)"
    and cp: "(False,s,t) \<in>
      critical_pairs string_rename (set R) (set R)"
  shows False
  using check_csr_orthogonal_critical_pairs[OF ok cp] by simp

end
