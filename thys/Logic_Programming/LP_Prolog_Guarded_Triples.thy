theory LP_Prolog_Guarded_Triples
  imports LP_Prolog_Success_Transfer LP_Dependency_Triple_Models
begin

text \<open>Guarded paths extend the shared dependency-triple semantics. Erasing
guards is available for structural Pi-DP children; arithmetic children retain
them. A successful-prefix contract never replaces the prefix's termination
obligation or the source graph's complete path-cover obligation.\<close>

definition lpp_lift_atom :: "'v lpp_success_atom \<Rightarrow> (string lp_cut_symbol,'v) lp_atom" where "lpp_lift_atom a = (LPCUser (fst a),snd a)"
definition lpp_lift_iatom :: "'w lpp_success_iatom \<Rightarrow> (string lp_cut_symbol,'w) lp_iatom" where "lpp_lift_iatom a = (LPCUser (fst a),snd a)"
definition lpp_erase_success where
  "lpp_erase_success P = map (\<lambda>(h,bs,gs). (lpp_lift_atom h,map lpp_lift_atom bs)) P"

lemma lpp_lift_atom_eval:
  "lp_atom_eval (lpp_lift_atom a) eta = lpp_lift_iatom (lpp_success_atom_eval a eta)"
  by (simp add: lp_atom_eval_def lpp_lift_atom_def lpp_lift_iatom_def lpp_success_atom_eval_def)

lemma lpp_guarded_success_erases:
  assumes success: "lpp_guarded_success P E a"
  shows "lp_answer_model (lpp_erase_success P) (lpp_lift_iatom a)"
  using success
proof (induct rule: lpp_guarded_success.induct)
  case (clause h bs gs eta)
  obtain i where bound: "i<length P" and row: "P!i=(h,bs,gs)"
    using clause.hyps(1) by (auto simp: in_set_conv_nth)
  have index: "i<length (lpp_erase_success P)"
    using bound by (simp add: lpp_erase_success_def)
  have erased: "lpp_erase_success P!i=(lpp_lift_atom h,map lpp_lift_atom bs)"
    using bound row by (simp add: lpp_erase_success_def)
  have body: "lp_answer_model (lpp_erase_success P) (lp_atom_eval b eta)"
    if "b\<in>set (snd (lpp_erase_success P!i))" for b
    using that clause.hyps by (auto simp: erased list_all_iff lpp_lift_atom_eval)
  have lifted: "lp_answer_model (lpp_erase_success P) (lp_atom_eval (lpp_lift_atom h) eta)"
    using lp_answer_model.clause[OF index body] by (simp add: erased)
  show ?case using lifted by (simp only: lpp_lift_atom_eval)
qed

type_synonym 'v lpp_guarded_triple =
  "'v lpp_success_atom \<times> 'v lpp_success_atom list \<times> 'v lpp_success_atom \<times> 'v lpp_success_guard list"

definition lpp_erase_triples where
  "lpp_erase_triples D = (\<lambda>(h,ps,b,gs). (lpp_lift_atom h,map lpp_lift_atom ps,lpp_lift_atom b)) ` D"

definition lpp_guarded_calls ::
  "'v lpp_guarded_triple set \<Rightarrow> 'v lpp_success_clause list \<Rightarrow>
    ((string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm \<Rightarrow> bool) \<Rightarrow>
    'w lpp_success_iatom rel" where
  "lpp_guarded_calls D P E = {(a,lpp_success_atom_eval b eta) |a h ps b gs sigma eta.
    (h,ps,b,gs)\<in>D \<and>
    (fst a,map (\<lambda>t. lp_isubst t sigma) (snd a))=lpp_success_atom_eval h eta \<and>
    list_all (lpp_success_guard_holds E eta) gs \<and>
    list_all (lpp_guarded_success P E) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)}"

lemma lpp_guarded_call_erases:
  assumes step: "(a,b)\<in>lpp_guarded_calls D P E"
  shows "(lpp_lift_iatom a,lpp_lift_iatom b)\<in>
    lp_triple_calls (lpp_erase_triples D) (lpp_erase_success P)"
proof -
  obtain h ps c gs sigma eta where member: "(h,ps,c,gs)\<in>D"
    and matching: "(fst a,map (\<lambda>t. lp_isubst t sigma) (snd a))=lpp_success_atom_eval h eta"
    and b: "b=lpp_success_atom_eval c eta"
    and models: "list_all (lpp_guarded_success P E) (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using step by (auto simp: lpp_guarded_calls_def)
  have triple: "(lpp_lift_atom h,map lpp_lift_atom ps,lpp_lift_atom c)\<in>lpp_erase_triples D"
    unfolding lpp_erase_triples_def
    by (rule image_eqI[where x="(h,ps,c,gs)"]) (use member in auto)
  have match: "lp_iatom_subst (lpp_lift_iatom a) sigma=lp_atom_eval (lpp_lift_atom h) eta"
    using matching by (simp add: lpp_lift_atom_eval lpp_lift_iatom_def lp_iatom_subst_def lpp_success_atom_eval_def)
  have body: "lp_answer_model (lpp_erase_success P) (lp_atom_eval g eta)"
    if present: "g\<in>set (map lpp_lift_atom ps)" for g
  proof -
    obtain d where member: "d\<in>set ps" and g: "g=lpp_lift_atom d" using present by (auto simp only: set_map)
    have success: "lpp_guarded_success P E (lpp_success_atom_eval d eta)"
      using models member by (simp add: list_all_iff)
    have model: "lp_answer_model (lpp_erase_success P) (lpp_lift_iatom (lpp_success_atom_eval d eta))"
      by (rule lpp_guarded_success_erases[OF success])
    show ?thesis using model by (simp only: g lpp_lift_atom_eval)
  qed
  show ?thesis using lp_triple_calls_modelI[OF triple match body]
    by (simp only: b lpp_lift_atom_eval)
qed

definition lpp_check_path_types ::
  "lpp_success_transfers \<Rightarrow> 'v lpp_success_atom list \<Rightarrow> 'v lpp_success_guard list \<Rightarrow>
    'v lpp_transfer_fact list \<Rightarrow> bool" where
  "lpp_check_path_types T ps gs fs = lpp_check_transfer_facts T (('''',[])::'v lpp_success_atom) [] ps gs [] fs"

lemma lpp_check_path_types_sound:
  fixes ps :: "'v lpp_success_atom list" and P :: "'v lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T P receipts"
    and checked: "lpp_check_path_types T ps gs fs"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and prefix: "list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b eta) ps)"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_integer_known (map lpp_transfer_variable fs) eta"
proof -
  have helpers: "list_all (\<lambda>b. lpp_transfer_holds T (lpp_success_atom_eval b eta)) ps"
    using lpp_check_transfer_program_sound[OF program evaluation] prefix
    by (auto simp: list_all_iff)
  have checked': "lpp_check_transfer_facts T (('''',[])::'v lpp_success_atom) [] ps gs [] fs"
    using checked by (simp add: lpp_check_path_types_def)
  have entry: "lpp_integer_positions [] (snd (lpp_success_atom_eval ('''',[]) eta))"
    by (simp add: lpp_integer_positions_def)
  have known: "lpp_integer_known [] eta" by (simp add: lpp_integer_known_def)
  show ?thesis using lpp_check_transfer_facts_sound[OF checked' entry known guards helpers evaluation]
    by simp
qed

lemma lpp_typed_successor_simulation_SN:
  assumes target: "SN S"
    and typed: "\<And>a b. (a,b)\<in>R \<Longrightarrow> T b"
    and simulate: "\<And>a b. (a,b)\<in>R \<Longrightarrow> T a \<Longrightarrow> (project a,project b)\<in>S"
  shows "SN R"
proof -
  have typed_sn: "SN_on R {a}" if "T a" for a
  proof -
    have all: "\<And>x. SN_on S {x} \<Longrightarrow> \<forall>a. T a \<longrightarrow> project a=x \<longrightarrow> SN_on R {a}"
    proof -
      fix x assume sn: "SN_on S {x}"
      show "\<forall>a. T a \<longrightarrow> project a=x \<longrightarrow> SN_on R {a}"
      proof (rule SN_on_induct[OF sn singletonI], intro allI impI)
        fix x a
        assume ih: "\<And>y. (x,y)\<in>S \<Longrightarrow> \<forall>a. T a \<longrightarrow> project a=y \<longrightarrow> SN_on R {a}"
          and ta: "T a" and px: "project a=x"
        show "SN_on R {a}"
        proof (rule step_reflects_SN_on)
          fix b assume ab: "(a,b)\<in>R"
          have edge: "(x,project b)\<in>S" using simulate[OF ab ta] px by simp
          show "SN_on R {b}" using ih[OF edge] typed[OF ab] by blast
        qed
      qed
    qed
    show ?thesis using all[of "project a"] target that by (auto simp: SN_defs)
  qed
  have "SN_on R {a}" for a
    by (rule step_reflects_SN_on) (use typed typed_sn in blast)
  then show ?thesis by (simp add: SN_defs)
qed

corollary lpp_guarded_calls_structural_SN:
  fixes E :: "(string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm \<Rightarrow> bool"
  assumes sn: "SN (lp_triple_calls (lpp_erase_triples D) (lpp_erase_success P) :: (string lp_cut_symbol,'w) lp_iatom rel)"
  shows "SN (lpp_guarded_calls D P E)"
  by (rule lpp_typed_successor_simulation_SN[where T="\<lambda>_. True" and project=lpp_lift_iatom, OF sn])
    (auto intro: lpp_guarded_call_erases)

ML \<open>
val checked = [@{thm lpp_guarded_success_erases}, @{thm lpp_guarded_call_erases},
  @{thm lpp_check_path_types_sound}, @{thm lpp_typed_successor_simulation_SN},
  @{thm lpp_guarded_calls_structural_SN}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted guarded triple dependency" else ();
\<close>


end
