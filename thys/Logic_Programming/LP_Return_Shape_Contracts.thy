theory LP_Return_Shape_Contracts
  imports LP_Return_Shape_Facts
begin

definition lp_return_args_facts where
  "lp_return_args_facts fuel G shapes ts = lp_return_merge_facts
    (map (\<lambda>(shape,t). lp_return_shape_facts fuel G shape t) (zip shapes ts))"

lemma lp_return_args_facts_sound:
  assumes "list_all2 (lp_return_shape_holds G) shapes (map (\<lambda>t. lp_ieval t rho) ts)"
  shows "lp_return_facts_valid G rho (lp_return_args_facts fuel G shapes ts)"
proof -
  have valid: "lp_return_facts_valid G rho (lp_return_shape_facts fuel G (shapes!i) (ts!i))"
    if "i<length ts" for i
  proof (rule lp_return_shape_facts_sound)
    show "lp_return_shape_holds G (shapes!i) (lp_ieval (ts!i) rho)"
      using assms that by (auto simp: list_all2_conv_all_nth)
  qed
  show ?thesis unfolding lp_return_args_facts_def
    by (rule lp_return_merge_facts_sound)
      (use assms valid in \<open>auto simp: list_all_iff list_all2_conv_all_nth in_set_zip\<close>)
qed

lemma lp_return_args_check_sound:
  assumes known: "lp_return_shape_known G known rho"
    and checked: "list_all2 (lp_return_shape_check fuel G known) shapes ts"
  shows "list_all2 (lp_return_shape_holds G) shapes (map (\<lambda>t. lp_ieval t rho) ts)"
  using checked lp_return_shape_check_sound[OF _ known]
  by (auto simp: list_all2_conv_all_nth)

definition lp_return_mode_facts where
  "lp_return_mode_facts fuel G mode a known = (case mode of (f,inputs,outputs) \<Rightarrow>
    if fst a=f \<and> length inputs=length (snd a) \<and> length outputs=length (snd a) \<and>
      list_all2 (lp_return_shape_check fuel G known) inputs (snd a)
    then lp_return_args_facts fuel G outputs (snd a) else Some [])"

lemma lp_return_mode_facts_sound:
  assumes contracts: "lp_return_contracts G modes (lp_atom_eval a rho)"
    and member: "mode\<in>set modes"
    and known: "lp_return_shape_known G known rho"
  shows "lp_return_facts_valid G rho (lp_return_mode_facts fuel G mode a known)"
proof -
  obtain f inputs outputs where mode: "mode=(f,inputs,outputs)" by (cases mode) auto
  show ?thesis
  proof (cases "fst a=f \<and> length inputs=length (snd a) \<and> length outputs=length (snd a) \<and>
      list_all2 (lp_return_shape_check fuel G known) inputs (snd a)")
    case False then show ?thesis by (auto simp: lp_return_mode_facts_def mode)
  next
    case True
    have inputs: "list_all2 (lp_return_shape_holds G) inputs (map (\<lambda>t. lp_ieval t rho) (snd a))"
      by (rule lp_return_args_check_sound[where fuel=fuel, OF known]) (use True in simp)
    have contract: "lp_return_shape_contract G inputs outputs (lp_atom_eval a rho)"
      using contracts member True mode by (fastforce simp: lp_return_contracts_def lp_atom_eval_def)
    have outputs: "list_all2 (lp_return_shape_holds G) outputs (map (\<lambda>t. lp_ieval t rho) (snd a))"
      using contract inputs True by (simp add: lp_return_shape_contract_def lp_atom_eval_def)
    show ?thesis using lp_return_args_facts_sound[OF outputs]
      by (simp add: lp_return_mode_facts_def mode True)
  qed
qed

fun lp_return_shape_transfer where
  "lp_return_shape_transfer fuel G modes a None = None"
| "lp_return_shape_transfer fuel G modes a (Some known) =
    lp_return_merge_facts (Some known # map (\<lambda>m. lp_return_mode_facts fuel G m a known) modes)"

lemma lp_return_shape_transfer_sound:
  assumes contracts: "lp_return_contracts G modes (lp_atom_eval a rho)"
    and valid: "lp_return_facts_valid G rho facts"
  shows "lp_return_facts_valid G rho (lp_return_shape_transfer fuel G modes a facts)"
proof (cases facts)
  case None then show ?thesis using valid by (simp add: lp_return_facts_valid_def)
next
  case (Some known)
  have known: "lp_return_shape_known G known rho"
    using valid Some by (simp add: lp_return_facts_valid_def)
  have all: "list_all (lp_return_facts_valid G rho)
    (Some known # map (\<lambda>m. lp_return_mode_facts fuel G m a known) modes)"
    using valid Some lp_return_mode_facts_sound[OF contracts _ known]
    by (auto simp: list_all_iff)
  show ?thesis unfolding Some lp_return_shape_transfer.simps
    by (rule lp_return_merge_facts_sound[OF all])
qed

fun lp_return_shape_flow where
  "lp_return_shape_flow fuel G modes [] known = known"
| "lp_return_shape_flow fuel G modes (a#rest) known =
    lp_return_shape_flow fuel G modes rest (lp_return_shape_transfer fuel G modes a known)"

lemma lp_return_shape_flow_sound:
  "(\<forall>a\<in>set body. lp_return_contracts G modes (lp_atom_eval a rho)) \<Longrightarrow>
   lp_return_facts_valid G rho facts \<Longrightarrow>
   lp_return_facts_valid G rho (lp_return_shape_flow fuel G modes body facts)"
  by (induct body arbitrary: facts) (auto intro: lp_return_shape_transfer_sound)

definition lp_return_shape_clause_check where
  "lp_return_shape_clause_check fuel G modes c mode = (case mode of (f,inputs,outputs) \<Rightarrow>
    fst (fst c)\<noteq>f \<or> length inputs\<noteq>length (snd (fst c)) \<or>
    (length outputs=length (snd (fst c)) \<and>
     (case lp_return_shape_flow fuel G modes (snd c)
       (lp_return_args_facts fuel G inputs (snd (fst c))) of None \<Rightarrow> True
      | Some known \<Rightarrow> list_all2 (lp_return_shape_check fuel G known) outputs (snd (fst c)))))"

definition lp_return_shape_program_check where
  "lp_return_shape_program_check fuel G modes P =
    list_all (\<lambda>c. list_all (lp_return_shape_clause_check fuel G modes c) modes) P"

lemma lp_return_shape_clause_check_sound:
  fixes c :: "('f,'v) lp_clause"
  assumes checked: "list_all (lp_return_shape_clause_check fuel G modes c) modes"
  shows "lp_return_shape_clause G modes c"
  unfolding lp_return_shape_clause_def
proof (intro allI impI)
  fix rho :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assume body: "\<forall>b\<in>set (snd c). lp_return_contracts G modes (lp_atom_eval b rho)"
  have contract: "lp_return_shape_contract G inputs outputs (lp_atom_eval (fst c) rho)"
    if member: "(f,inputs,outputs)\<in>set modes"
      and predicate: "fst (lp_atom_eval (fst c) rho)=f" for f inputs outputs
  proof -
    have check: "lp_return_shape_clause_check fuel G modes c (f,inputs,outputs)"
      using checked member by (simp add: list_all_iff)
    have result: "length outputs=length (snd (lp_atom_eval (fst c) rho)) \<and>
        (list_all2 (lp_return_shape_holds G) inputs (snd (lp_atom_eval (fst c) rho)) \<longrightarrow>
         list_all2 (lp_return_shape_holds G) outputs (snd (lp_atom_eval (fst c) rho)))"
      if length: "length inputs=length (snd (lp_atom_eval (fst c) rho))"
    proof -
      have output_length: "length outputs=length (snd (lp_atom_eval (fst c) rho))"
        using check predicate length by (auto simp: lp_return_shape_clause_check_def lp_atom_eval_def)
      have returned: "list_all2 (lp_return_shape_holds G) outputs (snd (lp_atom_eval (fst c) rho))"
        if inputs: "list_all2 (lp_return_shape_holds G) inputs (snd (lp_atom_eval (fst c) rho))"
      proof -
        let ?facts = "lp_return_shape_flow fuel G modes (snd c)
          (lp_return_args_facts fuel G inputs (snd (fst c)))"
        have valid: "lp_return_facts_valid G rho ?facts"
          by (rule lp_return_shape_flow_sound[OF body]; rule lp_return_args_facts_sound)
            (use inputs in \<open>simp add: lp_atom_eval_def\<close>)
        obtain known where facts: "?facts=Some known" and known: "lp_return_shape_known G known rho"
          using valid by (cases ?facts) (auto simp: lp_return_facts_valid_def)
        have outputs: "list_all2 (lp_return_shape_check fuel G known) outputs (snd (fst c))"
          using check predicate length facts by (simp add: lp_return_shape_clause_check_def lp_atom_eval_def)
        show ?thesis using lp_return_args_check_sound[OF known outputs] by (simp add: lp_atom_eval_def)
      qed
      show ?thesis using output_length returned by blast
    qed
    show ?thesis using result by (simp add: lp_return_shape_contract_def)
  qed
  show "lp_return_contracts G modes (lp_atom_eval (fst c) rho)"
    using contract by (auto simp: lp_return_contracts_def)
qed

theorem lp_return_shape_program_check_sound:
  assumes checked: "lp_return_shape_program_check fuel G modes P"
  shows "lp_return_shape_model P G modes"
proof (rule lp_return_shape_clause_cover_sound)
  fix c assume member: "c\<in>set P"
  have local: "list_all (lp_return_shape_clause_check fuel G modes c) modes"
    using checked member by (simp add: lp_return_shape_program_check_def list_all_iff)
  show "lp_return_shape_clause G modes c"
    by (rule lp_return_shape_clause_check_sound[OF local])
qed

ML \<open>
val audited = [@{thm lp_return_shape_facts_sound}, @{thm lp_return_shape_transfer_sound},
  @{thm lp_return_shape_flow_sound}, @{thm lp_return_shape_program_check_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted successful-return contract dependency" else ();
\<close>

end
