theory LP_Ranked_Checker_Bridge
  imports LP_Ranked_Representation LP_Checker_Bridge
begin

fun logic_erase_atom :: "('s \<Rightarrow> 't) \<Rightarrow> ('p \<times> nat,'s) logic_atom \<Rightarrow> ('p,'t) logic_atom" where
  "logic_erase_atom g (LAtom p ts) = LAtom (fst p) (map g ts)"
lemma logic_unrank_rank_term[simp]: "logic_unrank_term (logic_rank_term t) = t"
  by (induct t) (auto simp: map_map o_def intro!: map_idI)
lemma logic_erase_rank_atom[simp]:
  "logic_erase_atom logic_unrank_term (logic_rank_atom a) = a"
  by (cases a) (simp add: logic_rank_atom_def map_map o_def)
lemma logic_erase_atom_subst:
  "logic_erase_atom logic_unrank_tree (logic_atom_map (logic_subst s) a) =
    logic_atom_map (logic_subst (logic_unrank_tree \<circ> s)) (logic_erase_atom logic_unrank_tree a)"
  by (cases a) (simp add: map_map o_def logic_unrank_subst)
lemma logic_erase_atom_eval:
  "logic_erase_atom logic_unrank_tree (logic_atom_map (logic_eval s) a) =
    logic_atom_map (logic_eval (logic_unrank_tree \<circ> s)) (logic_erase_atom logic_unrank_term a)"
  by (cases a) (simp add: map_map o_def logic_unrank_subst logic_unrank_embed)
lemma logic_erase_atom_embed:
  "logic_erase_atom logic_unrank_tree (logic_atom_map logic_embed a) =
    logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)"
  by (cases a) (simp add: map_map o_def logic_unrank_embed)
lemma logic_erase_rank_rename_subst:
  "logic_erase_atom logic_unrank_tree (logic_atom_map (logic_subst s)
      (logic_atom_map (logic_eval (LVar \<circ> r)) (logic_rank_atom a))) =
    logic_atom_map (logic_eval (logic_unrank_tree \<circ> s \<circ> r)) a"
  by (simp add: logic_erase_atom_subst logic_erase_atom_eval logic_atom_map_comp
    logic_subst_composition o_def)
lemma logic_unrank_ground[simp]: "logic_ground (logic_unrank_term t) = logic_ground t"
  by (induct t) (auto simp: list_all_iff)

lemma logic_ranked_step_native:
  assumes step: "logic_step snd D (logic_rank_program P) s t"
  shows "(logic_to_goals (map (logic_erase_atom logic_unrank_tree) s),
    logic_to_goals (map (logic_erase_atom logic_unrank_tree) t)) \<in> lp_ild (logic_to_program P)"
  using step
proof (cases rule: logic_step.cases)
  case (resolve h bs r a gs sigma)
  obtain h0 bs0 where member: "(h0,bs0)\<in>set P"
    and h: "h=logic_rank_atom h0" and bs: "bs=map logic_rank_atom bs0"
    using resolve by (auto simp: logic_rank_program_def)
  obtain c where c: "c<length P" "P!c=(h0,bs0)"
    using member by (auto simp: in_set_conv_nth)
  have index: "c<length (logic_to_program P)" using c by (simp add: logic_to_program_def)
  let ?raw = "logic_unrank_tree \<circ> sigma"
  have equation: "logic_atom_map (logic_subst sigma) a =
    logic_atom_map (logic_subst sigma) (logic_atom_map (logic_eval (LVar \<circ> r)) h)"
    using resolve unfolding logic_mgu_def by blast
  have raw_eq: "logic_atom_map (logic_subst ?raw) (logic_erase_atom logic_unrank_tree a) =
    logic_atom_map (logic_eval (?raw \<circ> r)) h0"
    using arg_cong[OF equation, where f="logic_erase_atom logic_unrank_tree"]
    by (simp add: h logic_erase_atom_subst logic_erase_atom_eval logic_atom_map_comp
      logic_subst_composition o_def)
  have native_eq: "lp_iatom_subst (logic_to_atom logic_to_native (logic_erase_atom logic_unrank_tree a))
      (logic_to_native \<circ> ?raw) =
    lp_atom_eval (fst (logic_to_program P!c)) (logic_to_native \<circ> (?raw \<circ> r))"
    using arg_cong[OF raw_eq, where f="logic_to_atom logic_to_native"]
    by (simp add: logic_atom_subst_translation logic_atom_eval_translation logic_to_program_def c)
  show ?thesis using lp_ild.resolve[OF index native_eq,
      where gs="logic_to_goals (map (logic_erase_atom logic_unrank_tree) gs)"] resolve
    by (simp add: h bs logic_to_goals_def logic_to_program_def c map_map o_def
      logic_erase_atom_subst logic_erase_rank_rename_subst[unfolded o_def]
      logic_atom_subst_translation logic_atom_eval_translation logic_erase_atom_eval
      logic_native_renamed_eval[unfolded o_def])
qed

lemma logic_ranked_native_termination:
  fixes P :: "('f,'v) logic_clause list"
  assumes native: "\<And>a :: ('f \<times> nat,('f \<times> nat,'v) fo_term) logic_atom. logic_query snd (q,length modes) modes a \<Longrightarrow>
    SN_on (lp_ild (logic_to_program P))
      {logic_to_goals [logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)]}"
  shows "logic_terminates_in snd D (logic_rank_program P) (q,length modes) modes"
proof (unfold logic_terminates_in_def, clarify)
  fix a s assume query: "logic_query snd (q,length modes) modes a"
    and init: "s 0=[logic_atom_map logic_embed a]"
    and steps: "\<forall>n. logic_step snd D (logic_rank_program P) (s n) (s (Suc n))"
  let ?f = "\<lambda>n. logic_to_goals (map (logic_erase_atom logic_unrank_tree) (s n))"
  have start: "?f 0 = logic_to_goals [logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)]"
    by (simp add: init logic_erase_atom_embed)
  have edges: "\<forall>n. (?f n,?f (Suc n))\<in>lp_ild (logic_to_program P)"
    by (intro allI; rule logic_ranked_step_native; rule spec[OF steps])
  have bad: "\<exists>f. f 0\<in>{logic_to_goals [logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)]} \<and>
      (\<forall>n. (f n,f (Suc n))\<in>lp_ild (logic_to_program P))"
    by (rule exI[of _ ?f]) (simp add: start edges)
  show False using native[OF query] bad unfolding SN_on_def by blast
qed

text \<open>This boundary theorem uses name/arity symbols and string variables
while its parser premise and checker call retain the existing representations.
The encoded source is valid independently of checker acceptance.\<close>
theorem lp_tocl09_ranked_category_yes:
  fixes P :: "((string,nat list) lab,string) logic_clause list"
  assumes parsed: "parse_xml_string lp_tocl09_parser xml =
    Right (logic_to_program P,outs,fallback,names,filters,(q,length modes,positions),prf)"
    and accepted: "check_lp_tocl09_xml xml"
    and modes: "set positions={i. i<length modes \<and> modes!i}"
  shows "logic_problem snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_finite_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_rational_terminates snd (logic_rank_program P) (q,length modes) modes \<and>
    lp_infinite_terminates snd (logic_rank_program P) (q,length modes) modes"
proof -
  have all: "logic_terminates_in snd D (logic_rank_program P) (q,length modes) modes" for D
  proof (rule logic_ranked_native_termination)
    fix a :: "((string,nat list) lab \<times> nat,((string,nat list) lab \<times> nat,string) fo_term) logic_atom"
    assume query: "logic_query snd (q,length modes) modes a"
    let ?ts = "map (to_term \<circ> logic_unrank_term) (logic_arguments a)"
    have len: "length ?ts=length modes" using query by (cases a) (simp add: logic_query_def)
    have gr: "ground (?ts!i)" if pos: "i\<in>set positions" and i: "i<length modes" for i
    proof -
      have length: "length (logic_arguments a)=length modes" using len by simp
      have mode: "modes!i" using modes pos by auto
      have constraint: "list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t)
        (zip (logic_arguments a) modes)" using query unfolding logic_query_def by blast
      have member: "(logic_arguments a!i,modes!i)\<in>set (zip (logic_arguments a) modes)"
        using i length by (auto simp: set_zip)
      have ground: "logic_ground (logic_arguments a!i)"
        using constraint member mode by (auto simp: list_all_iff)
      show ?thesis using ground i length
        by (simp add: logic_ground_translation[symmetric])
    qed
    have native: "SN_on (lp_ild (logic_to_program P)) {[(q,map (\<lambda>t. lp_ieval t LPIVar) ?ts)]}"
      by (rule check_lp_tocl09_xml_sound[OF parsed accepted len gr])
    show "SN_on (lp_ild (logic_to_program P))
      {logic_to_goals [logic_atom_map logic_embed (logic_erase_atom logic_unrank_term a)]}"
      using native query by (cases a)
        (simp add: logic_to_goals_def logic_query_def map_map o_def logic_embed_translation)
  qed
  show ?thesis using all logic_rank_problem[of P q modes]
    unfolding lp_finite_terminates_def lp_rational_terminates_def lp_infinite_terminates_def by blast
qed

ML \<open>
  val results = @{thms logic_rank_problem logic_ranked_step_native
    logic_ranked_native_termination lp_tocl09_ranked_category_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked LP YES: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Ranked LP YES: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Ranked LP YES oracle dependencies: " ^ commas names)
\<close>

end
