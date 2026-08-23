(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Guarded_List_Measure
  imports CSR_Checker_Extensions.CSR_Minimal_CSDP_Proofs
begin

text \<open>
  Semantic ranks for the common membership-guarded list pattern used by
  context-sensitive specifications.  The three mutually recursive sorts are
  kept semantic: the same constructor may build a finite list or a possibly
  infinite list depending on the demanded result sort.  Every recursive call
  is on a proper syntactic subterm, so the rank is executable and independent
  of a particular benchmark spelling.
\<close>

datatype csr_guard_sort = Guard_Nat | Guard_List | Guard_IList

fun csr_guard_rank ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   'f \<Rightarrow> 'f \<Rightarrow> csr_guard_sort \<Rightarrow>
   ('f,'v) term \<Rightarrow> nat option"
where
  "csr_guard_rank z su len ni co ta zs Guard_Nat (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_Nat (Fun f ts) =
    (if f = z \<and> ts = [] then Some 0
     else if f = su \<and> length ts = 1 then
       map_option Suc
         (csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0))
     else if f = len \<and> length ts = 1 then
       csr_guard_rank z su len ni co ta zs Guard_List (ts ! 0)
     else None)"
| "csr_guard_rank z su len ni co ta zs Guard_List (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_List (Fun f ts) =
    (if f = ni \<and> ts = [] then Some 0
     else if f = co \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow> map_option Suc
            (csr_guard_rank z su len ni co ta zs Guard_List (ts ! 1)))
     else if f = ta \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some n))
     else None)"
| "csr_guard_rank z su len ni co ta zs Guard_IList (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_IList (Fun f ts) =
    (if f = zs \<and> ts = [] then Some 0
     else if f = co \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some 0))
     else if f = ni \<and> ts = [] then Some 0
     else if f = ta \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some 0))
     else None)"

lemma csr_guard_rank_cons_list:
  assumes distinct: "co \<noteq> ni" "co \<noteq> ta"
    and arity: "csr_guard_rank z su len ni co ta zs Guard_Nat n = Some kn"
      "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
  shows "csr_guard_rank z su len ni co ta zs Guard_List
      (Fun co [n,l]) = Some (Suc kl)"
  using assms by simp

lemma csr_guard_rank_cons_list_strict:
  assumes distinct: "co \<noteq> ni" "co \<noteq> ta"
    and arity: "csr_guard_rank z su len ni co ta zs Guard_Nat n = Some kn"
      "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
  obtains k where
    "csr_guard_rank z su len ni co ta zs Guard_List
       (Fun co [n,l]) = Some k"
    "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
    "k > kl"
proof
  show "csr_guard_rank z su len ni co ta zs Guard_List
       (Fun co [n,l]) = Some (Suc kl)"
    by (rule csr_guard_rank_cons_list[OF distinct arity])
  show "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
    by (rule arity(2))
  show "Suc kl > kl" by simp
qed

text \<open>
  The executable processor will validate the recognizer/schema rules and use
  the following relation as its strict component.  Keeping it explicit makes
  mutation-negative tests possible before it is connected to CPF parsing.
\<close>

definition csr_guard_rank_gt where
  "csr_guard_rank_gt z su len ni co ta zs A =
    {(s,t). \<exists>m n.
      csr_guard_rank z su len ni co ta zs A s = Some m \<and>
      csr_guard_rank z su len ni co ta zs A t = Some n \<and> m > n}"

definition csr_guard_rank_ge where
  "csr_guard_rank_ge z su len ni co ta zs A =
    {(s,t). \<exists>m n.
      csr_guard_rank z su len ni co ta zs A s = Some m \<and>
      csr_guard_rank z su len ni co ta zs A t = Some n \<and> m \<ge> n}"

lemma csr_guard_rank_gt_ge_comp:
  "csr_guard_rank_gt z su len ni co ta zs A O
      csr_guard_rank_ge z su len ni co ta zs A
    \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
  unfolding csr_guard_rank_gt_def csr_guard_rank_ge_def by auto

lemma csr_guard_rank_ge_gt_comp:
  "csr_guard_rank_ge z su len ni co ta zs A O
      csr_guard_rank_gt z su len ni co ta zs A
    \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
  unfolding csr_guard_rank_gt_def csr_guard_rank_ge_def by auto

lemma csr_guard_rank_ge_refl_on:
  "{t. \<exists>n. csr_guard_rank z su len ni co ta zs A t = Some n}
    \<subseteq> {t. (t,t) \<in> csr_guard_rank_ge z su len ni co ta zs A}"
  unfolding csr_guard_rank_ge_def by auto

lemma SN_csr_guard_rank_gt:
  "SN (csr_guard_rank_gt z su len ni co ta zs A)"
proof -
  have sub: "csr_guard_rank_gt z su len ni co ta zs A
      \<subseteq> inv_image {(m,n). m > n}
        (the \<circ> csr_guard_rank z su len ni co ta zs A)"
    unfolding csr_guard_rank_gt_def inv_image_def by auto
  have "SN (inv_image {(m,n). m > n}
      (the \<circ> csr_guard_rank z su len ni co ta zs A))"
    by (rule SN_inv_image[OF SN_nat_gt])
  then show ?thesis by (rule SN_subset[OF _ sub])
qed

lemma SN_rel_csr_guard_rank:
  "SN_rel (csr_guard_rank_gt z su len ni co ta zs A)
    (csr_guard_rank_ge z su len ni co ta zs A)"
proof -
  let ?S = "csr_guard_rank_gt z su len ni co ta zs A"
  let ?NS = "csr_guard_rank_ge z su len ni co ta zs A"
  have compat: "?NS O ?S \<subseteq> ?S"
    by (rule csr_guard_rank_ge_gt_comp)
  have sn: "SN ((?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*)"
    by (rule compatible_SN'[OF compat SN_csr_guard_rank_gt])
  have sub: "?NS\<^sup>* O ?S O ?NS\<^sup>*
      \<subseteq> (?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*"
  proof -
    have ns: "?NS\<^sup>* \<subseteq> (?NS \<union> ?S)\<^sup>*"
      by (rule rtrancl_mono, auto)
    show ?thesis
      by (rule relcomp_mono[OF ns relcomp_mono[OF subset_refl ns]])
  qed
  show ?thesis unfolding SN_rel_defs by (rule SN_subset[OF sn sub])
qed

text \<open>
  This is the framework boundary needed by an executable guarded-list
  processor.  The checker may establish the two inclusions using a typed
  symbolic rank calculation; the generic CSR-DP soundness argument below is
  independent of the concrete recognizer names and rules.
\<close>

lemma finite_min_csr_dpp_by_guard_rank:
  assumes strict: "csr_min_pair_step shp \<mu> P R
      \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
    and weak: "csdp_step shp \<mu> R
      \<subseteq> csr_guard_rank_ge z su len ni co ta zs A"
  shows "finite_min_csr_dpp shp \<mu> P R"
  unfolding finite_min_csr_dpp_def
  by (rule SN_rel_mono[OF strict weak SN_rel_csr_guard_rank])

end
