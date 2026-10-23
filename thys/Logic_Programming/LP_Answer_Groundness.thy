theory LP_Answer_Groundness
  imports LP_SEG_Answers
begin

text \<open>Successful-answer semantics over possibly infinite runtime trees.
  This relation asserts a finite successful proof, not termination of search.
  It deliberately includes every clause and does not assume an occurs check.\<close>

inductive lp_answer_model ::
  "('f,'v) lp_clause list \<Rightarrow> ('f,'w) lp_iatom \<Rightarrow> bool"
  for P where
  clause: "c < length P \<Longrightarrow>
    (\<And>b. b \<in> set (snd (P!c)) \<Longrightarrow> lp_answer_model P (lp_atom_eval b \<nu>)) \<Longrightarrow>
    lp_answer_model P (lp_atom_eval (fst (P!c)) \<nu>)"

lemma lp_answer_model_subst:
  "lp_answer_model P a \<Longrightarrow> lp_answer_model P (lp_iatom_subst a \<sigma>)"
proof (induct rule: lp_answer_model.induct)
  case (clause c \<nu>)
  have eq: "lp_iatom_subst (lp_atom_eval b \<nu>) \<sigma> =
    lp_atom_eval b (\<lambda>x. lp_isubst (\<nu> x) \<sigma>)" for b
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def lp_ieval_subst)
  show ?case unfolding eq
    by (rule lp_answer_model.clause[OF clause.hyps(1)])
      (use clause.hyps in \<open>simp add: eq\<close>)
qed

lemma lp_answer_steps_model:
  assumes path: "((gs,\<rho>),([],\<eta>)) \<in> (lp_seg_answer_step P)\<^sup>*"
  shows "\<exists>\<delta>. \<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<delta>) \<and>
    (\<forall>a\<in>set gs. lp_answer_model P (lp_iatom_subst a \<delta>))"
  using path
proof (induct rule: converse_rtrancl_induct2)
  case refl
  show ?case by (rule exI[of _ LPIVar]) simp
next
  case (step gs \<rho> hs \<tau>)
  obtain c a tail \<sigma> \<nu> where c: "c < length P"
    and gs: "gs = a # tail"
    and eq: "lp_iatom_subst a \<sigma> = lp_atom_eval (fst (P!c)) \<nu>"
    and hs: "hs = map (\<lambda>b. lp_atom_eval b \<nu>) (snd (P!c)) @
      map (\<lambda>b. lp_iatom_subst b \<sigma>) tail"
    and tau: "\<tau> = (\<lambda>x. lp_isubst (\<rho> x) \<sigma>)"
    using step.hyps(1) by (cases rule: lp_seg_answer_step.cases) blast
  obtain \<delta> where eta: "\<eta> = (\<lambda>x. lp_isubst (\<tau> x) \<delta>)"
    and model: "\<forall>b\<in>set hs. lp_answer_model P (lp_iatom_subst b \<delta>)"
    using step.hyps(3) by blast
  have body: "lp_answer_model P (lp_atom_eval b (\<lambda>x. lp_isubst (\<nu> x) \<delta>))"
    if "b \<in> set (snd (P!c))" for b
  proof -
    have "lp_answer_model P (lp_iatom_subst (lp_atom_eval b \<nu>) \<delta>)"
      using model that by (auto simp only: hs set_append set_map)
    then show ?thesis by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def lp_ieval_subst)
  qed
  have head: "lp_answer_model P (lp_iatom_subst (lp_iatom_subst a \<sigma>) \<delta>)"
    using lp_answer_model.clause[OF c body] eq
    by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def lp_ieval_subst)
  have tails: "lp_answer_model P (lp_iatom_subst (lp_iatom_subst b \<sigma>) \<delta>)"
    if "b\<in>set tail" for b
    using model that by (auto simp only: hs set_append set_map)
  show ?case
    by (rule exI[of _ "\<lambda>x. lp_isubst (\<sigma> x) \<delta>"])
      (use eta tails head in
        \<open>auto simp: tau gs hs lp_iatom_subst_def o_def lp_seg_isubst_comp\<close>)
qed

datatype 'f lp_ground_mode = LPGroundMode 'f nat "nat list" "nat list"

fun lp_ground_matches where
  "lp_ground_matches (LPGroundMode f n pins pouts) a = (fst a = f \<and> length (snd a) = n)"

fun lp_ground_inputs where
  "lp_ground_inputs (LPGroundMode f n pins pouts) = pins"

fun lp_ground_outputs where
  "lp_ground_outputs (LPGroundMode f n pins pouts) = pouts"

definition lp_ground_vars where
  "lp_ground_vars a positions = (\<Union>i\<in>set positions. vars_term (snd a ! i))"

definition lp_ground_positions where
  "lp_ground_positions a positions = (\<forall>i\<in>set positions. lp_seg_ground (snd a ! i))"

definition lp_ground_contract where
  "lp_ground_contract m a = (lp_ground_matches m a \<longrightarrow>
    lp_ground_positions a (lp_ground_inputs m) \<longrightarrow>
    lp_ground_positions a (lp_ground_outputs m))"

fun lp_ground_valid_mode where
  "lp_ground_valid_mode (LPGroundMode f n pins pouts) =
    (list_all (\<lambda>i. i < n) pins \<and> list_all (\<lambda>i. i < n) pouts)"

definition lp_ground_transfer where
  "lp_ground_transfer modes a G = G \<union>
    (\<Union>m\<in>set modes.
      if lp_ground_matches m a \<and> lp_ground_vars a (lp_ground_inputs m) \<subseteq> G
      then lp_ground_vars a (lp_ground_outputs m) else {})"

fun lp_ground_flow where
  "lp_ground_flow modes [] G = G"
| "lp_ground_flow modes (a#rest) G =
    lp_ground_flow modes rest (lp_ground_transfer modes a G)"

definition lp_ground_check where
  "lp_ground_check P modes =
    (list_all lp_ground_valid_mode modes \<and>
     (\<forall>m\<in>set modes. \<forall>c\<in>set P. lp_ground_matches m (fst c) \<longrightarrow>
       lp_ground_vars (fst c) (lp_ground_outputs m) \<subseteq>
       lp_ground_flow modes (snd c) (lp_ground_vars (fst c) (lp_ground_inputs m))))"

lemma lp_ground_transfer_code[code]:
  "lp_ground_transfer modes a G = G \<union> Union (set (map (\<lambda>m.
    if lp_ground_matches m a \<and> lp_ground_vars a (lp_ground_inputs m) \<subseteq> G
    then lp_ground_vars a (lp_ground_outputs m) else {}) modes))"
  by (simp add: lp_ground_transfer_def)

lemma lp_ground_check_code[code]:
  "lp_ground_check P modes = (list_all lp_ground_valid_mode modes \<and>
    list_all (\<lambda>m. list_all (\<lambda>c. \<not>lp_ground_matches m (fst c) \<or>
      lp_ground_vars (fst c) (lp_ground_outputs m) \<subseteq>
      lp_ground_flow modes (snd c) (lp_ground_vars (fst c) (lp_ground_inputs m))) P) modes)"
  by (auto simp: lp_ground_check_def list_all_iff)

lemma lp_ground_positions_eval:
  assumes bounds: "\<forall>i\<in>set positions. i < length (snd a)"
  shows "lp_ground_positions (lp_atom_eval a \<nu>) positions =
    (\<forall>x\<in>lp_ground_vars a positions. lp_seg_ground (\<nu> x))"
  using bounds by (auto simp: lp_ground_positions_def lp_ground_vars_def
    lp_atom_eval_def lp_seg_ground_eval)

lemma lp_ground_matches_eval[simp]:
  "lp_ground_matches m (lp_atom_eval a \<nu>) = lp_ground_matches m a"
  by (cases m) (simp add: lp_atom_eval_def)

lemma lp_ground_transfer_sound:
  assumes valid: "list_all lp_ground_valid_mode modes"
    and contracts: "\<forall>m\<in>set modes. lp_ground_contract m (lp_atom_eval a \<nu>)"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<nu> x)"
  shows "\<forall>x\<in>lp_ground_transfer modes a G. lp_seg_ground (\<nu> x)"
proof -
  have out_known: "\<forall>x\<in>lp_ground_vars a (lp_ground_outputs m). lp_seg_ground (\<nu> x)"
    if m: "m\<in>set modes" and match: "lp_ground_matches m a"
      and inputs: "lp_ground_vars a (lp_ground_inputs m) \<subseteq> G" for m
  proof -
    have bounds: "\<forall>i\<in>set (lp_ground_inputs m). i < length (snd a)"
      "\<forall>i\<in>set (lp_ground_outputs m). i < length (snd a)"
      using valid m match by (cases m; auto simp: list_all_iff)+
    have contract: "lp_ground_contract m (lp_atom_eval a \<nu>)" using contracts m by blast
    show ?thesis using contract ground inputs
      by (auto simp: lp_ground_contract_def match lp_ground_positions_eval[OF bounds(1)]
        lp_ground_positions_eval[OF bounds(2)])
  qed
  show ?thesis using ground out_known by (auto simp: lp_ground_transfer_def split: if_splits)
qed

lemma lp_ground_flow_sound:
  assumes "list_all lp_ground_valid_mode modes"
    "\<forall>a\<in>set body. \<forall>m\<in>set modes. lp_ground_contract m (lp_atom_eval a \<nu>)"
    "\<forall>x\<in>G. lp_seg_ground (\<nu> x)"
  shows "\<forall>x\<in>lp_ground_flow modes body G. lp_seg_ground (\<nu> x)"
  using assms
proof (induct body arbitrary: G)
  case Nil then show ?case by simp
next
  case (Cons a body)
  have transferred: "\<forall>x\<in>lp_ground_transfer modes a G. lp_seg_ground (\<nu> x)"
    by (rule lp_ground_transfer_sound[OF Cons.prems(1) _ Cons.prems(3)])
      (use Cons.prems(2) in simp)
  show ?case using Cons.hyps[OF Cons.prems(1) _ transferred] Cons.prems(2) by simp
qed

theorem lp_ground_check_model:
  assumes checked: "lp_ground_check P modes" and success: "lp_answer_model P a"
  shows "\<forall>m\<in>set modes. lp_ground_contract m a"
  using success
proof (induct rule: lp_answer_model.induct)
  case (clause c \<nu>)
  show ?case
  proof (intro ballI, unfold lp_ground_contract_def, intro impI)
    fix m assume m: "m\<in>set modes"
      and match: "lp_ground_matches m (lp_atom_eval (fst (P!c)) \<nu>)"
      and in_known: "lp_ground_positions (lp_atom_eval (fst (P!c)) \<nu>) (lp_ground_inputs m)"
    have valid: "list_all lp_ground_valid_mode modes"
      using checked by (simp add: lp_ground_check_def)
    have bounds: "\<forall>i\<in>set (lp_ground_inputs m). i < length (snd (fst (P!c)))"
      "\<forall>i\<in>set (lp_ground_outputs m). i < length (snd (fst (P!c)))"
      using valid m match by (cases m; auto simp: list_all_iff lp_atom_eval_def)+
    have ground: "\<forall>x\<in>lp_ground_vars (fst (P!c)) (lp_ground_inputs m). lp_seg_ground (\<nu> x)"
      using in_known by (simp add: lp_ground_positions_eval[OF bounds(1)])
    have flow: "\<forall>x\<in>lp_ground_flow modes (snd (P!c))
      (lp_ground_vars (fst (P!c)) (lp_ground_inputs m)). lp_seg_ground (\<nu> x)"
      by (rule lp_ground_flow_sound[OF valid _ ground]) (use clause.hyps in blast)
    have member: "P!c\<in>set P" by (rule nth_mem[OF clause.hyps(1)])
    have allowed: "lp_ground_vars (fst (P!c)) (lp_ground_outputs m) \<subseteq>
      lp_ground_flow modes (snd (P!c)) (lp_ground_vars (fst (P!c)) (lp_ground_inputs m))"
      using checked m member match unfolding lp_ground_check_def
      by (simp only: lp_ground_matches_eval)
    show "lp_ground_positions (lp_atom_eval (fst (P!c)) \<nu>) (lp_ground_outputs m)"
      using allowed flow by (auto simp: lp_ground_positions_eval[OF bounds(2)])
  qed
qed

theorem lp_ground_check_answers:
  assumes checked: "lp_ground_check P modes"
    and path: "((map (\<lambda>a. lp_atom_eval a \<rho>) goals,\<rho>),([],\<eta>))
      \<in> (lp_seg_answer_step P)\<^sup>*"
    and ground: "\<forall>x\<in>G. lp_seg_ground (\<rho> x)"
  shows "\<forall>x\<in>lp_ground_flow modes goals G. lp_seg_ground (\<eta> x)"
proof -
  obtain \<delta> where eta: "\<eta> = (\<lambda>x. lp_isubst (\<rho> x) \<delta>)"
    and models: "\<forall>a\<in>set (map (\<lambda>a. lp_atom_eval a \<rho>) goals).
      lp_answer_model P (lp_iatom_subst a \<delta>)"
    using lp_answer_steps_model[OF path] by blast
  have model: "lp_answer_model P (lp_atom_eval a \<eta>)" if "a\<in>set goals" for a
  proof -
    have "lp_answer_model P (lp_iatom_subst (lp_atom_eval a \<rho>) \<delta>)"
      using models that by auto
    then show ?thesis by (simp add: eta lp_atom_eval_def lp_iatom_subst_def o_def lp_ieval_subst)
  qed
  have contracts: "\<forall>a\<in>set goals. \<forall>m\<in>set modes. lp_ground_contract m (lp_atom_eval a \<eta>)"
    using lp_ground_check_model[OF checked model] by blast
  have preserved: "\<forall>x\<in>G. lp_seg_ground (\<eta> x)"
    using ground by (simp add: eta lp_seg_ground_subst)
  show ?thesis by (rule lp_ground_flow_sound[OF _ contracts preserved])
    (use checked in \<open>simp add: lp_ground_check_def\<close>)
qed

end
