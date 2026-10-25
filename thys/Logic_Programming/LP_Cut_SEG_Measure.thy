theory LP_Cut_SEG_Measure
  imports LP_Cut_SEG_Control LP_SEG_Finite_Measure
begin

text \<open>Empty-stack leaves have no observation interface. They need no entry
template, but cannot have outgoing control clauses. Every recursive boundary
and successful-return predicate remains active and must preserve the template.
This is checked on clauses, independently of native node numbering.\<close>

definition lpc_seg_template_program_on where
  "lpc_seg_template_program_on active templates Q = list_all (\<lambda>(h,bs).
    fst h\<in>active \<and> length bs=1 \<and>
    (fst (hd bs)\<in>active \<longrightarrow> lpc_seg_template_edge templates h (hd bs))) Q"

lemma lpc_seg_template_step_on:
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and step: "([a],gs)\<in>lp_ild Q"
  shows "fst a\<in>active \<and> (\<exists>b. gs=[b] \<and>
    (fst b\<in>active \<longrightarrow> lp_seg_ground (lpc_seg_template_value templates a) \<longrightarrow>
      lpc_seg_template_value templates b = lpc_seg_template_value templates a))"
proof -
  obtain c eta sigma where c: "c<length Q"
    and unified: "lp_iatom_subst a sigma = lp_atom_eval (fst (Q!c)) eta"
    and gs: "gs=map (\<lambda>b. lp_atom_eval b eta) (snd (Q!c))"
    using step by (cases rule: lp_ild.cases) auto
  have len: "length (snd (Q!c))=1" and active: "fst (fst (Q!c))\<in>active"
    and edge: "fst (hd (snd (Q!c)))\<in>active \<longrightarrow>
      lpc_seg_template_edge templates (fst (Q!c)) (hd (snd (Q!c)))"
    using checked c by (auto simp: lpc_seg_template_program_on_def list_all_iff split_def)
  obtain b where body: "snd (Q!c)=[b]" using len by (cases "snd (Q!c)") auto
  have source: "fst a\<in>active" using active unified by (simp add: lp_iatom_subst_def lp_atom_eval_def prod_eq_iff)
  have equal: "lpc_seg_template_value templates (lp_atom_eval b eta) = lpc_seg_template_value templates a"
    if target: "fst b\<in>active" and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
    by (rule lpc_seg_template_edge_preserves[OF _ unified ground]) (use edge body target in simp)
  show ?thesis using source gs body equal by (auto simp: lp_atom_eval_def)
qed

lemma lpc_seg_template_path_on:
  assumes checked: "lpc_seg_template_program_on active templates Q"
    and path: "([a],gs)\<in>(lp_ild Q)\<^sup>*"
    and ground: "lp_seg_ground (lpc_seg_template_value templates a)"
  shows "\<exists>b. gs=[b] \<and> (fst b\<in>active \<longrightarrow>
    lpc_seg_template_value templates b = lpc_seg_template_value templates a)"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by auto
next
  case (step ys zs)
  obtain b where ys: "ys=[b]" and same: "fst b\<in>active \<longrightarrow>
    lpc_seg_template_value templates b = lpc_seg_template_value templates a"
    using step.hyps by blast
  have edge: "([b],zs)\<in>lp_ild Q" using step.hyps(2) ys by simp
  obtain c where active: "fst b\<in>active" and zs: "zs=[c]"
    and equal: "fst c\<in>active \<longrightarrow> lp_seg_ground (lpc_seg_template_value templates b) \<longrightarrow>
      lpc_seg_template_value templates c = lpc_seg_template_value templates b"
    using lpc_seg_template_step_on[OF checked edge] by blast
  have known: "lp_seg_ground (lpc_seg_template_value templates b)" using ground same active by simp
  show ?case using zs equal known same active by auto
qed

definition lpc_seg_position_template where
  "lpc_seg_position_template vs t = map_term id
    (\<lambda>x. case map_of (zip vs [0..<length vs]) x of None \<Rightarrow> 0 | Some n \<Rightarrow> n) t"

definition lpc_seg_templates where
  "lpc_seg_templates entries f = (case map_of (map (\<lambda>(f,vs,t). (f,lpc_seg_position_template vs t)) entries) f of
    None \<Rightarrow> Fun LPCTruth [] | Some t \<Rightarrow> t)"

definition lpc_seg_check_templates where
  "lpc_seg_check_templates entries Q = (distinct (map fst entries) \<and>
    list_all (\<lambda>(f,vs,t). distinct vs \<and> vars_term t \<subseteq> set vs) entries \<and>
    lpc_seg_template_program_on (set (map fst entries)) (lpc_seg_templates entries) Q)"

lemma lpc_seg_check_templates_code[code]:
  "lpc_seg_check_templates entries Q = (distinct (map fst entries) \<and>
    list_all (\<lambda>(f,vs,t). distinct vs \<and> vars_term t \<subseteq> set vs) entries \<and>
    list_all (\<lambda>(h,bs). List.member (map fst entries) (fst h) \<and> length bs=1 \<and>
      (List.member (map fst entries) (fst (hd bs)) \<longrightarrow>
       lpc_seg_template_edge (lpc_seg_templates entries) h (hd bs))) Q)"
  by (simp add: lpc_seg_check_templates_def lpc_seg_template_program_on_def)

lemma lpc_seg_checked_template_path:
  assumes checked: "lpc_seg_check_templates entries Q"
    and path: "([a],[b])\<in>(lp_ild Q)\<^sup>*"
    and ground: "lp_seg_ground (lpc_seg_template_value (lpc_seg_templates entries) a)"
    and active: "fst b\<in>set (map fst entries)"
  shows "lpc_seg_template_value (lpc_seg_templates entries) b =
    lpc_seg_template_value (lpc_seg_templates entries) a"
proof -
  have program: "lpc_seg_template_program_on (set (map fst entries)) (lpc_seg_templates entries) Q"
    using checked by (simp add: lpc_seg_check_templates_def)
  show ?thesis using lpc_seg_template_path_on[OF program path ground] active by auto
qed

lemma lpc_seg_template_lookup:
  assumes lookup: "map_of entries f=Some (vs,t)"
  shows "lpc_seg_templates entries f=lpc_seg_position_template vs t"
  using lookup
proof (induct entries)
  case Nil then show ?case by simp
next
  case (Cons entry entries)
  obtain g us u where entry: "entry=(g,us,u)" by (cases entry) auto
  show ?case using Cons by (cases "g=f") (auto simp: entry lpc_seg_templates_def)
qed

lemma lpc_seg_template_lookup_active:
  assumes "map_of entries f=Some (vs,t)"
  shows "f\<in>set (map fst entries)"
  using map_of_SomeD[OF assms] by force

lemma lpc_seg_template_lookup_valid:
  assumes checked: "lpc_seg_check_templates entries Q"
    and lookup: "map_of entries f=Some (vs,t)"
  shows "distinct vs \<and> vars_term t \<subseteq> set vs"
  using checked map_of_SomeD[OF lookup]
  by (auto simp: lpc_seg_check_templates_def list_all_iff)

end
