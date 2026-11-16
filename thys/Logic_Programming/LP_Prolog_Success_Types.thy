theory LP_Prolog_Success_Types
  imports LP_Prolog_Arithmetic
begin

text \<open>Successful helper calls justify return facts by induction on finite
successful derivations. Recursive use of a summary is not a termination proof.
The complete success program is checked; there is no selected-clause shortcut.\<close>

type_synonym 'v lpp_success_atom = "string \<times> (string lp_cut_symbol,'v) term list"
type_synonym 'w lpp_success_iatom = "string \<times> (string lp_cut_symbol,'w) lp_iterm list"

datatype 'v lpp_success_guard =
    LPPSInteger "(string lp_cut_symbol,'v) term"
  | LPPSEvaluates "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"
  | LPPSOpaque "(string lp_cut_symbol,'v) term"
  | LPPSNumeric nat "(string lp_cut_symbol,'v) term" "(string lp_cut_symbol,'v) term"

type_synonym 'v lpp_success_clause =
  "'v lpp_success_atom \<times> 'v lpp_success_atom list \<times> 'v lpp_success_guard list"
type_synonym lpp_success_summary = "(string \<times> nat) \<Rightarrow> nat list"

definition lpp_is_integer where
  "lpp_is_integer t = (\<exists>n. t=lpp_integer_value n)"

text \<open>A successful numerical test retains finite operands and successful
operand evaluations. Its order consequence is conditional on integer values;
finite ground expressions and floating values do not imply integer typing.
Groundness makes this contract stable under later helper substitutions.\<close>
fun lpp_success_numeric_relation :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "lpp_success_numeric_relation 0 n m = (n<m)"
| "lpp_success_numeric_relation (Suc 0) n m = (n\<le>m)"
| "lpp_success_numeric_relation (Suc (Suc 0)) n m = (n=m)"
| "lpp_success_numeric_relation (Suc (Suc (Suc 0))) n m = (n\<noteq>m)"
| "lpp_success_numeric_relation _ n m = False"

fun lpp_success_guard_holds where
  "lpp_success_guard_holds E eta (LPPSInteger t) = lpp_is_integer (lp_ieval t eta)"
| "lpp_success_guard_holds E eta (LPPSEvaluates e t) = E (lp_ieval e eta) (lp_ieval t eta)"
| "lpp_success_guard_holds E eta (LPPSOpaque t) = True"
| "lpp_success_guard_holds E eta (LPPSNumeric c a b) =
    (lp_seg_ground (lp_ieval a eta) \<and> lp_seg_ground (lp_ieval b eta) \<and>
     (\<exists>u v. E (lp_ieval a eta) u \<and> E (lp_ieval b eta) v \<and>
     (\<forall>n m. u = lpp_integer_value n \<longrightarrow>
       v = lpp_integer_value m \<longrightarrow> lpp_success_numeric_relation c n m)))"

definition lpp_eval_integer_contract :: "'v itself \<Rightarrow>
  ((string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm \<Rightarrow> bool) \<Rightarrow> bool" where
  "lpp_eval_integer_contract TYPE('v) E = (\<forall>(K::'v list) e eta t.
    lpp_expression_check K e \<longrightarrow> lpp_integer_known K eta \<longrightarrow>
    E (lp_ieval (lpp_expression_term e) eta) t \<longrightarrow> lpp_is_integer t)"

definition lpp_success_atom_eval where
  "lpp_success_atom_eval a eta = (fst a,map (\<lambda>t. lp_ieval t eta) (snd a))"

definition lpp_success_summary_holds where
  "lpp_success_summary_holds S a =
    (\<forall>i\<in>set (S (fst a,length (snd a))). i<length (snd a) \<and> lpp_is_integer (snd a!i))"


lemma lpp_is_integer_subst:
  "lpp_is_integer t \<Longrightarrow> lpp_is_integer (lp_isubst t sigma)"
  by (unfold lpp_is_integer_def) (metis lpp_integer_value_subst)

lemma lpp_success_summary_subst:
  "lpp_success_summary_holds S (p,ts) \<Longrightarrow>
   lpp_success_summary_holds S (p,map (\<lambda>t. lp_isubst t sigma) ts)"
  by (auto simp: lpp_success_summary_holds_def intro: lpp_is_integer_subst)

inductive lpp_guarded_success ::
  "'v lpp_success_clause list \<Rightarrow>
   ((string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm \<Rightarrow> bool) \<Rightarrow>
   'w lpp_success_iatom \<Rightarrow> bool" for P E where
  clause: "(h,bs,gs)\<in>set P \<Longrightarrow>
    list_all (lpp_success_guard_holds E eta) gs \<Longrightarrow>
    list_all (lpp_guarded_success P E) (map (\<lambda>b. lpp_success_atom_eval b eta) bs) \<Longrightarrow>
    lpp_guarded_success P E (lpp_success_atom_eval h eta)"

text \<open>The witness records each addition to the integer environment. A
helper position must be present in the proposed summary; an evaluation must
be bound to the actual source expression.\<close>

datatype 'v lpp_integer_fact = LPPSGuard nat 'v | LPPSHelper nat nat 'v
  | LPPSEvaluation nat "'v lpp_integer_expression" 'v

fun lpp_fact_variable where
  "lpp_fact_variable (LPPSGuard i x) = x"
| "lpp_fact_variable (LPPSHelper i j x) = x"
| "lpp_fact_variable (LPPSEvaluation i e x) = x"

fun lpp_check_integer_fact where
  "lpp_check_integer_fact S bs gs K (LPPSGuard i x) =
    (i<length gs \<and> gs!i=LPPSInteger (Var x))"
| "lpp_check_integer_fact S bs gs K (LPPSHelper i j x) =
    (i<length bs \<and> j<length (snd (bs!i)) \<and>
     j\<in>set (S (fst (bs!i),length (snd (bs!i)))) \<and> snd (bs!i)!j=Var x)"
| "lpp_check_integer_fact S bs gs K (LPPSEvaluation i e x) =
    (i<length gs \<and> gs!i=LPPSEvaluates (lpp_expression_term e) (Var x) \<and> lpp_expression_check K e)"

lemma lpp_check_integer_fact_sound:
  fixes gs :: "'v lpp_success_guard list"
  assumes checked: "lpp_check_integer_fact S bs gs K evidence"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_success_summary_holds S (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_is_integer (eta (lpp_fact_variable evidence))"
proof (cases evidence)
  case (LPPSGuard i x)
  have bound: "i<length gs" using checked LPPSGuard by simp
  have "lpp_success_guard_holds E eta (gs!i)"
    using guards bound by (meson list_all_iff nth_mem)
  then show ?thesis using checked LPPSGuard by auto
next
  case (LPPSHelper i j x)
  have bound: "i<length bs" using checked LPPSHelper by simp
  have "lpp_success_summary_holds S (lpp_success_atom_eval (bs!i) eta)"
    using helpers bound by (meson list_all_iff nth_mem)
  then show ?thesis using checked LPPSHelper
    by (auto simp: lpp_success_summary_holds_def lpp_success_atom_eval_def)
next
  case (LPPSEvaluation i e x)
  have bound: "i<length gs" using checked LPPSEvaluation by simp
  have guard: "lpp_success_guard_holds E eta (gs!i)"
    using guards bound by (meson list_all_iff nth_mem)
  have eval: "E (lp_ieval (lpp_expression_term e) eta) (eta x)"
    using guard checked LPPSEvaluation by auto
  have check: "lpp_expression_check K e" using checked LPPSEvaluation by simp
  show ?thesis using evaluation check known eval LPPSEvaluation
    by (auto simp: lpp_eval_integer_contract_def)
qed

fun lpp_check_integer_facts where
  "lpp_check_integer_facts S bs gs K [] = True"
| "lpp_check_integer_facts S bs gs K (f#fs) =
    (lpp_check_integer_fact S bs gs K f \<and>
     lpp_check_integer_facts S bs gs (lpp_fact_variable f#K) fs)"

lemma lpp_check_integer_facts_sound:
  fixes fs :: "'v lpp_integer_fact list"
  assumes checked: "lpp_check_integer_facts S bs gs K fs"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_success_summary_holds S (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_integer_known (map lpp_fact_variable fs @ K) eta"
  using checked known
proof (induct fs arbitrary: K)
  case Nil then show ?case by simp
next
  case (Cons f fs)
  have one: "lpp_is_integer (eta (lpp_fact_variable f))"
    by (rule lpp_check_integer_fact_sound[OF _ Cons.prems(2) guards helpers evaluation])
      (use Cons.prems in simp)
  have extended: "lpp_integer_known (lpp_fact_variable f#K) eta"
    using one Cons.prems(2) by (auto simp: lpp_integer_known_def lpp_is_integer_def)
  have all: "lpp_integer_known (map lpp_fact_variable fs @ (lpp_fact_variable f#K)) eta"
    by (rule Cons.hyps[OF _ extended]) (use Cons.prems in simp)
  show ?case using all by (auto simp: lpp_integer_known_def)
qed

datatype 'v lpp_integer_output = LPPSVariable 'v | LPPSConstant int
fun lpp_integer_output_term where
  "lpp_integer_output_term (LPPSVariable x) = Var x"
| "lpp_integer_output_term (LPPSConstant n) = lpp_integer_term n"
fun lpp_check_integer_output where
  "lpp_check_integer_output K (LPPSVariable x) = (x\<in>set K)"
| "lpp_check_integer_output K (LPPSConstant n) = True"

lemma lpp_check_integer_output_sound:
  "lpp_check_integer_output K output \<Longrightarrow> lpp_integer_known K eta \<Longrightarrow>
   lpp_is_integer (lp_ieval (lpp_integer_output_term output) eta)"
  by (cases "output") (auto simp: lpp_integer_known_def lpp_is_integer_def)


definition lpp_check_success_clause where
  "lpp_check_success_clause S c fs os = (case c of (h,bs,gs) \<Rightarrow>
    lpp_check_integer_facts S bs gs [] fs \<and>
    length os=length (S (fst h,length (snd h))) \<and>
    list_all (\<lambda>j. let i=S (fst h,length (snd h))!j in
      i<length (snd h) \<and> snd h!i=lpp_integer_output_term (os!j) \<and>
      lpp_check_integer_output (map lpp_fact_variable fs) (os!j)) [0..<length os])"

lemma lpp_check_success_clause_sound:
  fixes h :: "'v lpp_success_atom"
  assumes checked: "lpp_check_success_clause S (h,bs,gs) fs os"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_success_summary_holds S (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_success_summary_holds S (lpp_success_atom_eval h eta)"
proof -
  have check: "lpp_check_integer_facts S bs gs [] fs"
    using checked by (simp add: lpp_check_success_clause_def)
  have empty: "lpp_integer_known [] eta" by (simp add: lpp_integer_known_def)
  have known: "lpp_integer_known (map lpp_fact_variable fs) eta"
    using lpp_check_integer_facts_sound[OF check empty guards helpers evaluation] by simp
  have established: "i<length (snd h) \<and> lpp_is_integer (lp_ieval (snd h!i) eta)"
    if member: "i\<in>set (S (fst h,length (snd h)))" for i
  proof -
    obtain j where j: "j<length (S (fst h,length (snd h)))"
      and i: "i=S (fst h,length (snd h))!j"
      using member by (auto simp: in_set_conv_nth)
    have bound: "j<length os" using checked j by (simp add: lpp_check_success_clause_def)
    have row: "i<length (snd h)" "snd h!i=lpp_integer_output_term (os!j)"
      "lpp_check_integer_output (map lpp_fact_variable fs) (os!j)"
      using checked bound i by (auto simp: lpp_check_success_clause_def list_all_iff Let_def)
    show ?thesis using lpp_check_integer_output_sound[OF row(3) known] row by simp
  qed
  show ?thesis using established
    by (auto simp: lpp_success_summary_holds_def lpp_success_atom_eval_def)
qed

definition lpp_check_success_program where
  "lpp_check_success_program S P proofs =
    (length P=length proofs \<and> list_all (\<lambda>i.
       lpp_check_success_clause S (P!i) (fst (proofs!i)) (snd (proofs!i))) [0..<length P])"

theorem lpp_check_success_program_sound:
  fixes P :: "'v lpp_success_clause list"
  assumes checked: "lpp_check_success_program S P proofs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
    and success: "lpp_guarded_success P E a"
  shows "lpp_success_summary_holds S a"
proof -
  have local: "lpp_success_summary_holds S (lpp_success_atom_eval h eta)"
    if clause: "(h,bs,gs)\<in>set P"
      and guards: "list_all (lpp_success_guard_holds E eta) gs"
      and helpers: "list_all (\<lambda>b. lpp_success_summary_holds S (lpp_success_atom_eval b eta)) bs"
    for h bs gs eta
  proof -
    obtain i where i: "i<length P" and pi: "P!i=(h,bs,gs)"
      using clause by (auto simp: in_set_conv_nth)
    have rows: "list_all (\<lambda>i. lpp_check_success_clause S (P!i) (fst (proofs!i)) (snd (proofs!i))) [0..<length P]"
      using checked unfolding lpp_check_success_program_def by blast
    have member: "i\<in>set [0..<length P]" using i by simp
    have raw: "lpp_check_success_clause S (P!i) (fst (proofs!i)) (snd (proofs!i))"
      using rows member by (meson list_all_iff)
    have check: "lpp_check_success_clause S (h,bs,gs) (fst (proofs!i)) (snd (proofs!i))"
      using raw pi by simp
    show ?thesis by (rule lpp_check_success_clause_sound[OF check guards helpers evaluation])
  qed
  show ?thesis using success
    by (induction rule: lpp_guarded_success.induct)
      (auto intro: local simp: list_all_iff)
qed


end
