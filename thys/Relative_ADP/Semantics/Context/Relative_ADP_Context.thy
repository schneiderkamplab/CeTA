theory Relative_ADP_Context
  imports Relative_ADP_Global_Dev.Relative_ADP_Global
begin

definition relative_origin_productive ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow> bool" where
  "relative_origin_productive R B D \<longleftrightarrow>
    (\<forall>s q. q \<in> adp_defined_positions D s \<longrightarrow>
      s |_ q \<in> Tinf (relstep R B) \<longrightarrow>
      (\<exists>u q'. relative_origin_block R B D s u q q q' \<and>
        q' \<in> adp_defined_positions D u \<and>
        u |_ q' \<in> Tinf (relstep R B)))"

definition adp_minimal_marked ::
  "('f, 'v) trs \<Rightarrow> ('f, 'v) trs \<Rightarrow> 'f set \<Rightarrow>
    ('f adp_symbol, 'v) term set" where
  "adp_minimal_marked R B D =
    {sh. \<exists>q. q \<in> sharp_positions sh \<and>
      q \<in> adp_defined_positions D (erase_adp_term sh) \<and>
      erase_adp_term sh |_ q \<in> Tinf (relstep R B)}"

lemma relative_origin_productive_gives_adp_progress:
  assumes productive: "relative_origin_productive R B D"
    and source: "sh \<in> adp_minimal_marked R B D"
  obtains uh where
    "uh \<in> adp_minimal_marked R B D"
    "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
proof -
  from source obtain q where marked: "q \<in> sharp_positions sh"
    and defined: "q \<in> adp_defined_positions D (erase_adp_term sh)"
    and minimal: "erase_adp_term sh |_ q \<in> Tinf (relstep R B)"
    unfolding adp_minimal_marked_def by blast
  obtain u q' where block:
      "relative_origin_block R B D (erase_adp_term sh) u q q q'"
    and defined': "q' \<in> adp_defined_positions D u"
    and minimal': "u |_ q' \<in> Tinf (relstep R B)"
    using productive defined minimal
    unfolding relative_origin_productive_def by blast
  obtain uh where erased: "erase_adp_term uh = u"
    and adp_block: "(sh, uh) \<in> adp_productive_block_rel
      (canonical_adps 1 D R) (canonical_adps 2 D B)"
    and marked': "q' \<in> sharp_positions uh"
    by (rule relative_origin_block_lifts[OF block refl marked marked])
  have target: "uh \<in> adp_minimal_marked R B D"
    unfolding adp_minimal_marked_def
    by (rule CollectI, rule exI[of _ q'])
       (use marked' defined' minimal' erased in auto)
  show thesis by (rule that[OF target adp_block])
qed

lemma Tinf_relstep_defined_root_exact:
  assumes "wf_trs (R \<union> B)" and "t \<in> Tinf (relstep R B)"
  shows "\<exists>f. defined (R \<union> B) f \<and> root t = Some f"
  using assms(1)
    Tinf_imp_SN_nr_first_root_step_rel[
      of t False "{}" B "{}" R,
      unfolded qrstep_rstep_conv nrqrstep_nrrstep rqrstep_rrstep_conv,
      OF assms(2)]
    nrrsteps_imp_eq_root_arg_rsteps[of t _ "R \<union> B"] assms
  by (auto simp: nrrstep_union wf_trs_def defined_def elim!: rrstepE)
     (case_tac l; auto)+

lemma Tinf_root_is_adp_defined:
  assumes wf: "wf_trs (R \<union> B)"
    and minimal: "t \<in> Tinf (relstep R B)"
  shows "[] \<in> adp_defined_positions (adp_defined_symbols (R \<union> B)) t"
proof -
  obtain f n where root: "root t = Some (f, n)"
    and root_defined: "defined (R \<union> B) (f, n)"
    using Tinf_relstep_defined_root_exact[OF wf minimal] by force
  then obtain ts where t: "t = Fun f ts" and n: "n = length ts"
    by (cases t) auto
  from root_defined obtain l r where rule: "(l, r) \<in> R \<union> B"
    and lhs: "root l = Some (f, n)"
    unfolding defined_def by blast
  from lhs obtain us where l: "l = Fun f us"
    by (cases l) auto
  have fD: "f \<in> adp_defined_symbols (R \<union> B)"
    unfolding adp_defined_symbols_def using rule l by blast
  show ?thesis
    unfolding adp_defined_positions_def t using fD by simp
qed

theorem relative_origin_productive_chain_criterion:
  assumes wf: "wf_trs (R \<union> B)"
    and productive: "relative_origin_productive R B
      (adp_defined_symbols (R \<union> B))"
    and not_sn: "\<not> SN_rel (rstep R) (rstep B)"
  shows "\<not> adp_problem_SN (canonical_relative_adp_problem R B)"
proof -
  let ?D = "adp_defined_symbols (R \<union> B)"
  let ?P = "canonical_adps 1 ?D R"
  let ?Q = "canonical_adps 2 ?D B"
  obtain t where minimal: "t \<in> Tinf (relstep R B)"
    using not_SN_imp_Tinf[OF not_sn[unfolded SN_relto_SN_rel_conv[symmetric]]]
    by blast
  let ?sh = "annotate_term {[]} t"
  have root_fun: "[] \<in> fun_poss t"
    using Tinf_root_is_adp_defined[OF wf minimal]
      adp_defined_positions_fun_poss by blast
  have marked: "[] \<in> sharp_positions ?sh"
    using sharp_positions_annotate_term[OF root_fun, of "{[]}"] by simp
  have initial: "?sh \<in> adp_minimal_marked R B ?D"
    unfolding adp_minimal_marked_def
    apply (rule CollectI, rule exI[of _ "[]"])
    using marked Tinf_root_is_adp_defined[OF wf minimal] minimal by simp
  have progress: "\<And>sh. sh \<in> adp_minimal_marked R B ?D \<Longrightarrow>
      \<exists>uh. uh \<in> adp_minimal_marked R B ?D \<and>
        (sh, uh) \<in> adp_productive_block_rel ?P ?Q"
    using relative_origin_productive_gives_adp_progress[OF productive] by blast
  have "\<not> adp_problem_SN (?P, ?Q)"
    by (rule serial_productive_blocks_not_SN[OF initial progress])
  then show ?thesis
    unfolding canonical_relative_adp_problem_def Let_def .
qed

end
