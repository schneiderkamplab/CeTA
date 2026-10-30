theory LP_Prolog_Success_Transfer
  imports LP_Prolog_Success_Types
begin

type_synonym lpp_success_transfers = "(string \<times> nat) \<Rightarrow> (nat list \<times> nat list) list"
definition lpp_integer_positions where
  "lpp_integer_positions indices ts = (\<forall>i\<in>set indices. i<length ts \<and> lpp_is_integer (ts!i))"
definition lpp_transfer_holds where
  "lpp_transfer_holds T a = (\<forall>(required,outs)\<in>set (T (fst a,length (snd a))).
    lpp_integer_positions required (snd a) \<longrightarrow> lpp_integer_positions outs (snd a))"
definition lpp_unconditional_summary where
  "lpp_unconditional_summary T sig = concat (map snd (filter (\<lambda>r. fst r=[]) (T sig)))"

lemma lpp_transfer_unconditional:
  "lpp_transfer_holds T a \<Longrightarrow> lpp_success_summary_holds (lpp_unconditional_summary T) a"
  by (auto simp: lpp_transfer_holds_def lpp_unconditional_summary_def
    lpp_success_summary_holds_def lpp_integer_positions_def split: prod.splits)

lemma lpp_check_output_positions:
  assumes length: "length ws=length indices"
    and checked: "list_all (\<lambda>j. indices!j<length ts \<and>
      ts!(indices!j)=lpp_integer_output_term (ws!j) \<and> lpp_check_integer_output K (ws!j)) [0..<length ws]"
    and known: "lpp_integer_known K eta"
  shows "lpp_integer_positions indices (map (\<lambda>t. lp_ieval t eta) ts)"
proof (unfold lpp_integer_positions_def, intro ballI)
  fix i assume "i\<in>set indices"
  then obtain j where j: "j<length indices" and i: "i=indices!j" by (auto simp: in_set_conv_nth)
  have mem: "j\<in>set [0..<length ws]" using j length by simp
  have row: "indices!j<length ts \<and> ts!(indices!j)=lpp_integer_output_term (ws!j) \<and>
    lpp_check_integer_output K (ws!j)" by (rule bspec[OF _ mem]) (use checked in \<open>simp only: list_all_iff\<close>)
  have typed: "lpp_is_integer (lp_ieval (lpp_integer_output_term (ws!j)) eta)"
    by (rule lpp_check_integer_output_sound[OF _ known]) (use row in simp)
  show "i<length (map (\<lambda>t. lp_ieval t eta) ts) \<and>
    lpp_is_integer (map (\<lambda>t. lp_ieval t eta) ts!i)" using row typed i by simp
qed

datatype 'v lpp_transfer_fact = LPPTInput nat 'v | LPPTBase "'v lpp_integer_fact"
  | LPPTHelper nat nat nat 'v "'v lpp_integer_output list"
fun lpp_transfer_variable where
  "lpp_transfer_variable (LPPTInput i x) = x"
| "lpp_transfer_variable (LPPTBase f) = lpp_fact_variable f"
| "lpp_transfer_variable (LPPTHelper i r j x ws) = x"

fun lpp_check_transfer_fact where
  "lpp_check_transfer_fact T h required bs gs K (LPPTInput i x) =
    (i\<in>set required \<and> i<length (snd h) \<and> snd h!i=Var x)"
| "lpp_check_transfer_fact T h required bs gs K (LPPTBase f) =
    lpp_check_integer_fact (lpp_unconditional_summary T) bs gs K f"
| "lpp_check_transfer_fact T h required bs gs K (LPPTHelper i r j x ws) =
    (i<length bs \<and> r<length (T (fst (bs!i),length (snd (bs!i)))) \<and>
     (let rule=T (fst (bs!i),length (snd (bs!i)))!r in
       j\<in>set (snd rule) \<and> j<length (snd (bs!i)) \<and> snd (bs!i)!j=Var x \<and>
       length ws=length (fst rule) \<and>
       list_all (\<lambda>k. fst rule!k<length (snd (bs!i)) \<and>
         snd (bs!i)!(fst rule!k)=lpp_integer_output_term (ws!k) \<and>
         lpp_check_integer_output K (ws!k)) [0..<length ws]))"

lemma lpp_check_transfer_fact_sound:
  fixes h :: "'v lpp_success_atom"
  assumes checked: "lpp_check_transfer_fact T h required bs gs K evidence"
    and entry: "lpp_integer_positions required (snd (lpp_success_atom_eval h eta))"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_transfer_holds T (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_is_integer (eta (lpp_transfer_variable evidence))"
proof (cases evidence)
  case (LPPTInput i x)
  then show ?thesis using checked entry
    by (auto simp: lpp_integer_positions_def lpp_success_atom_eval_def)
next
  case (LPPTBase f)
  have ordinary: "list_all (\<lambda>b. lpp_success_summary_holds (lpp_unconditional_summary T) (lpp_success_atom_eval b eta)) bs"
    using helpers by (auto simp: list_all_iff intro: lpp_transfer_unconditional)
  have check: "lpp_check_integer_fact (lpp_unconditional_summary T) bs gs K f" using checked LPPTBase by simp
  show ?thesis using lpp_check_integer_fact_sound[OF check known guards ordinary evaluation] LPPTBase by simp
next
  case (LPPTHelper i r j x ws)
  let ?a = "bs!i"
  let ?rules = "T (fst ?a,length (snd ?a))"
  let ?rule = "?rules!r"
  have bound: "i<length bs" "r<length ?rules" and out: "j\<in>set (snd ?rule)"
    and pos: "j<length (snd ?a)" "snd ?a!j=Var x"
    and len: "length ws=length (fst ?rule)"
    and rows: "list_all (\<lambda>k. fst ?rule!k<length (snd ?a) \<and>
      snd ?a!(fst ?rule!k)=lpp_integer_output_term (ws!k) \<and>
      lpp_check_integer_output K (ws!k)) [0..<length ws]"
    using checked LPPTHelper by (auto simp: Let_def)
  have inputs: "lpp_integer_positions (fst ?rule) (map (\<lambda>t. lp_ieval t eta) (snd ?a))"
    by (rule lpp_check_output_positions[OF len rows known])
  have helper: "lpp_transfer_holds T (lpp_success_atom_eval ?a eta)"
    using helpers bound(1) by (meson list_all_iff nth_mem)
  have rule: "?rule\<in>set ?rules" using bound(2) by (rule nth_mem)
  have outputs: "lpp_integer_positions (snd ?rule) (map (\<lambda>t. lp_ieval t eta) (snd ?a))"
    using helper rule inputs by (auto simp: lpp_transfer_holds_def lpp_success_atom_eval_def split: prod.splits)
  show ?thesis using outputs out pos LPPTHelper
    by (auto simp: lpp_integer_positions_def)
qed

fun lpp_check_transfer_facts where
  "lpp_check_transfer_facts T h required bs gs K [] = True"
| "lpp_check_transfer_facts T h required bs gs K (f#fs) =
    (lpp_check_transfer_fact T h required bs gs K f \<and>
      lpp_check_transfer_facts T h required bs gs (lpp_transfer_variable f#K) fs)"

lemma lpp_check_transfer_facts_sound:
  fixes h :: "'v lpp_success_atom"
  assumes checked: "lpp_check_transfer_facts T h required bs gs K fs"
    and entry: "lpp_integer_positions required (snd (lpp_success_atom_eval h eta))"
    and known: "lpp_integer_known K eta"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_transfer_holds T (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_integer_known (map lpp_transfer_variable fs @ K) eta"
  using checked known
proof (induct fs arbitrary: K)
  case Nil then show ?case by simp
next
  case (Cons f fs)
  have one: "lpp_is_integer (eta (lpp_transfer_variable f))"
    by (rule lpp_check_transfer_fact_sound[OF _ entry Cons.prems(2) guards helpers evaluation])
      (use Cons.prems in simp)
  have extended: "lpp_integer_known (lpp_transfer_variable f#K) eta"
    using one Cons.prems(2) by (auto simp: lpp_integer_known_def lpp_is_integer_def)
  have all: "lpp_integer_known (map lpp_transfer_variable fs @ (lpp_transfer_variable f#K)) eta"
    by (rule Cons.hyps[OF _ extended]) (use Cons.prems in simp)
  show ?case using all by (auto simp: lpp_integer_known_def)
qed


definition lpp_check_transfer_clause where
  "lpp_check_transfer_clause T c policy fs os = (case c of (h,bs,gs) \<Rightarrow>
    lpp_check_transfer_facts T h (fst policy) bs gs [] fs \<and>
    length os=length (snd policy) \<and>
    list_all (\<lambda>j. snd policy!j<length (snd h) \<and>
      snd h!(snd policy!j)=lpp_integer_output_term (os!j) \<and>
      lpp_check_integer_output (map lpp_transfer_variable fs) (os!j)) [0..<length os])"

lemma lpp_check_transfer_clause_sound:
  fixes h :: "'v lpp_success_atom"
  assumes checked: "lpp_check_transfer_clause T (h,bs,gs) (required,outs) fs os"
    and entry: "lpp_integer_positions required (snd (lpp_success_atom_eval h eta))"
    and guards: "list_all (lpp_success_guard_holds E eta) gs"
    and helpers: "list_all (\<lambda>b. lpp_transfer_holds T (lpp_success_atom_eval b eta)) bs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
  shows "lpp_integer_positions outs (snd (lpp_success_atom_eval h eta))"
proof -
  have check: "lpp_check_transfer_facts T h required bs gs [] fs"
    using checked by (simp add: lpp_check_transfer_clause_def)
  have empty: "lpp_integer_known [] eta" by (simp add: lpp_integer_known_def)
  have known: "lpp_integer_known (map lpp_transfer_variable fs) eta"
    using lpp_check_transfer_facts_sound[OF check entry empty guards helpers evaluation] by simp
  have len: "length os=length outs" and rows:
    "list_all (\<lambda>j. outs!j<length (snd h) \<and>
      snd h!(outs!j)=lpp_integer_output_term (os!j) \<and>
      lpp_check_integer_output (map lpp_transfer_variable fs) (os!j)) [0..<length os]"
    using checked by (auto simp: lpp_check_transfer_clause_def)
  show ?thesis using lpp_check_output_positions[OF len rows known]
    by (simp add: lpp_success_atom_eval_def)
qed

definition lpp_check_transfer_rows where
  "lpp_check_transfer_rows T c receipts = (case c of (h,bs,gs) \<Rightarrow>
    length receipts=length (T (fst h,length (snd h))) \<and>
    list_all (\<lambda>j. lpp_check_transfer_clause T c (T (fst h,length (snd h))!j)
      (fst (receipts!j)) (snd (receipts!j))) [0..<length receipts])"

definition lpp_check_transfer_program where
  "lpp_check_transfer_program T P proofs = (length P=length proofs \<and>
    list_all (\<lambda>i. lpp_check_transfer_rows T (P!i) (proofs!i)) [0..<length P])"

theorem lpp_check_transfer_program_sound:
  fixes P :: "'v lpp_success_clause list"
  assumes checked: "lpp_check_transfer_program T P proofs"
    and evaluation: "lpp_eval_integer_contract TYPE('v) E"
    and success: "lpp_guarded_success P E a"
  shows "lpp_transfer_holds T a"
proof -
  have local: "lpp_transfer_holds T (lpp_success_atom_eval h eta)"
    if clause: "(h,bs,gs)\<in>set P"
      and guards: "list_all (lpp_success_guard_holds E eta) gs"
      and helpers: "list_all (\<lambda>b. lpp_transfer_holds T (lpp_success_atom_eval b eta)) bs"
    for h bs gs eta
  proof -
    obtain i where i: "i<length P" and pi: "P!i=(h,bs,gs)"
      using clause by (auto simp: in_set_conv_nth)
    have all: "list_all (\<lambda>i. lpp_check_transfer_rows T (P!i) (proofs!i)) [0..<length P]"
      using checked unfolding lpp_check_transfer_program_def by blast
    have mem: "i\<in>set [0..<length P]" using i by simp
    have raw: "lpp_check_transfer_rows T (P!i) (proofs!i)"
      by (rule bspec[OF _ mem]) (use all in \<open>simp only: list_all_iff\<close>)
    have row: "lpp_check_transfer_rows T (h,bs,gs) (proofs!i)" using raw pi by simp
    have implication: "lpp_integer_positions outs (snd (lpp_success_atom_eval h eta))"
      if member: "(required,outs)\<in>set (T (fst h,length (snd h)))"
        and entry: "lpp_integer_positions required (snd (lpp_success_atom_eval h eta))"
      for required outs
    proof -
      obtain j where j: "j<length (T (fst h,length (snd h)))"
        and rule: "T (fst h,length (snd h))!j=(required,outs)"
        using member by (auto simp: in_set_conv_nth)
      have bound: "j<length (proofs!i)" using row j by (simp add: lpp_check_transfer_rows_def)
      have rows: "list_all (\<lambda>j. lpp_check_transfer_clause T (h,bs,gs) (T (fst h,length (snd h))!j)
        (fst (proofs!i!j)) (snd (proofs!i!j))) [0..<length (proofs!i)]"
        using row unfolding lpp_check_transfer_rows_def by auto
      have jm: "j\<in>set [0..<length (proofs!i)]" using bound by simp
      have raw: "lpp_check_transfer_clause T (h,bs,gs) (T (fst h,length (snd h))!j)
        (fst (proofs!i!j)) (snd (proofs!i!j))"
        by (rule bspec[OF _ jm]) (use rows in \<open>simp only: list_all_iff\<close>)
      have check: "lpp_check_transfer_clause T (h,bs,gs) (required,outs)
        (fst (proofs!i!j)) (snd (proofs!i!j))" using raw rule by simp
      show ?thesis by (rule lpp_check_transfer_clause_sound[OF check entry guards helpers evaluation])
    qed
    show ?thesis using implication
      by (auto simp: lpp_transfer_holds_def lpp_success_atom_eval_def split: prod.splits)
  qed
  show ?thesis using success
    by (induction rule: lpp_guarded_success.induct) (auto intro: local simp: list_all_iff)
qed

end
