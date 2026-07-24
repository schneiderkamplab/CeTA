theory RFC_Matchbounds_Ext
  imports SN.Matchbounds_Impl
begin

text \<open>
This session is a development layer for RFC match-bounds certification.
It is intentionally above the standard IsaFoR/CeTA sessions, so proof
iteration here does not invalidate the large IsaFoR_2 heap.

Once the RFC theorems are stable, they should be moved back into the
canonical Matchbounds/Proof_Checker theories and exported through the
standard unified CeTA checker.
\<close>

lemma sum_bind_split:
  "P (m \<bind> f) = ((\<forall>v. m = Inl v \<longrightarrow> P (Inl v)) \<and> (\<forall>v. m = Inr v \<longrightarrow> P (f v)))"
  by (cases m, auto)

lemma sum_bind_split_asm:
  "P (m \<bind> f) = (\<not> ((\<exists>v. m = Inl v \<and> \<not> P (Inl v)) \<or> (\<exists>x. m = Inr x \<and> \<not> P (f x))))"
  by (cases m, auto)

lemmas sum_bind_splits = sum_bind_split sum_bind_split_asm

fun rfc_word_term :: "'f list \<Rightarrow> 'v \<Rightarrow> ('f,'v)term"
where
  "rfc_word_term [] x = Var x"
| "rfc_word_term (f # fs) x = Fun f [rfc_word_term fs x]"

lemma vars_term_rfc_word_term[simp]:
  "vars_term (rfc_word_term w x) = {x}"
  by (induct w) auto

lemma map_vars_term_rfc_word_term[simp]:
  "map_vars_term h (rfc_word_term w x) = rfc_word_term w (h x)"
  by (induct w) auto

fun rfc_term_word :: "('f,string)term \<Rightarrow> ('f list \<times> string) option"
where
  "rfc_term_word (Var x) = Some ([],x)"
| "rfc_term_word (Fun f [t]) =
    (case rfc_term_word t of
      None \<Rightarrow> None
    | Some (w,x) \<Rightarrow> Some (f # w,x))"
| "rfc_term_word (Fun f ts) = None"

definition rfc_rule_words ::
  "('f,string)rule \<Rightarrow> ('f list \<times> 'f list) option"
where
  "rfc_rule_words lr \<equiv> (case lr of (l,r) \<Rightarrow>
    case (rfc_term_word l, rfc_term_word r) of
      (Some (lw,x), Some (rw,y)) \<Rightarrow>
        if x = y then Some (lw,rw) else None
    | _ \<Rightarrow> None)"

lemma rfc_term_word_sound:
  assumes "rfc_term_word t = Some (w,x)"
  shows "t = rfc_word_term w x"
  using assms
  by (induct t arbitrary: w x rule: rfc_term_word.induct)
    (auto split: option.splits prod.splits)

lemma rfc_rule_words_sound:
  assumes "rfc_rule_words lr = Some (lw,rw)"
  shows "\<exists>x.
    fst lr = rfc_word_term lw x \<and>
    snd lr = rfc_word_term rw x"
proof (cases lr)
  case (Pair l r)
  then obtain lx rx where
    left: "rfc_term_word l = Some (lw,lx)"
    and right: "rfc_term_word r = Some (rw,rx)"
    and same: "lx = rx"
    using assms unfolding rfc_rule_words_def
    by (auto split: option.splits prod.splits if_splits)
  have l: "l = rfc_word_term lw lx"
    by (rule rfc_term_word_sound[OF left])
  have r: "r = rfc_word_term rw rx"
    by (rule rfc_term_word_sound[OF right])
  show ?thesis
    using Pair same l r by auto
qed

definition lift_sig :: "nat \<Rightarrow> ('f \<times> nat) \<Rightarrow> (('f \<times> nat) \<times> nat)" where
  "lift_sig h fn = (case fn of (f,n) \<Rightarrow> ((f,h),n))"

definition unlift_sig :: "(('f \<times> nat) \<times> nat) \<Rightarrow> ('f \<times> nat)" where
  "unlift_sig fn = (case fn of ((f,h),n) \<Rightarrow> (f,n))"

lemma funas_term_lift_term:
  "funas_term (lift_term h t) = lift_sig h ` funas_term t"
  unfolding lift_sig_def
  by (induct t) auto

lemma funas_term_lift_sigI:
  assumes "fn \<in> funas_term t"
  shows "lift_sig h fn \<in> funas_term (lift_term h t)"
  using assms
  unfolding funas_term_map_funs_term lift_sig_def
  by (cases fn) auto

lemma unlift_sig_after_lift_sig[simp]:
  "unlift_sig (lift_sig h x) = x"
  unfolding lift_sig_def unlift_sig_def
  by (cases x) simp

definition rfc_initial_single_var ::
  "('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_single_var I \<equiv>
    list_all (\<lambda>t. length (remdups (vars_term_list t)) \<le> 1) I"

definition rfc_initial_covers ::
  "('f,string)rules \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_covers R I \<equiv>
    list_all (\<lambda>(l,r). r \<in> set I) R"

definition rfc_term_accepted_with_tail_states_impl ::
  "'f itself \<Rightarrow>
    ('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)term \<Rightarrow> bool"
where
  "rfc_term_accepted_with_tail_states_impl _ TA qfin t \<equiv>
    list_all (\<lambda>q.
      \<not> rs.isEmpty (rs.inter (ta_final_impl TA)
        (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
          (map_vars_term (\<lambda>_. q) (lift_term 0 t))))) qfin"

definition rfc_initial_accepted_with_tail_states_impl ::
  "'f itself \<Rightarrow>
    ('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_accepted_with_tail_states_impl T TA qfin I \<equiv>
    list_all (rfc_term_accepted_with_tail_states_impl T TA qfin) I"

definition rfc_word_reaches_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q \<Rightarrow> 'f list \<Rightarrow> 'q \<Rightarrow> bool"
where
  "rfc_word_reaches_impl TA q w p \<equiv>
    rs.memb p
      (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term w ''x''))))"

definition rfc_word_reaches_some_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> 'f list \<Rightarrow> 'q \<Rightarrow> bool"
where
  "rfc_word_reaches_some_impl TA qs w q \<equiv>
    \<not> list_all (\<lambda>m. \<not> rfc_word_reaches_impl TA q w m) qs"

definition rfc_rule_automaton_closed_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_automaton_closed_impl TA qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw,rw) \<Rightarrow>
        list_all (\<lambda>i.
          let prefix = take i lw; suffix = drop i lw
          in list_all (\<lambda>q. list_all (\<lambda>m. list_all (\<lambda>p.
            \<not> (rfc_word_reaches_impl TA q suffix m \<and>
              rfc_word_reaches_impl TA m prefix p) \<or>
            rfc_word_reaches_impl TA q rw p) qs) qs) qs)
          [1..<Suc (length lw)])"

definition rfc_automaton_closed_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_automaton_closed_impl TA qs R \<equiv>
    list_all (rfc_rule_automaton_closed_impl TA qs) R"

definition rfc_rule_lhs_suffix_total_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_lhs_suffix_total_impl TA qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw,rw) \<Rightarrow>
        lw \<noteq> [] \<and>
        list_all (\<lambda>i.
          list_all (rfc_word_reaches_some_impl TA qs (drop i lw)) qs)
          [1..<length lw])"

definition rfc_lhs_suffix_total_impl ::
  "('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_lhs_suffix_total_impl TA qs R \<equiv>
    list_all (rfc_rule_lhs_suffix_total_impl TA qs) R"

lemma rfc_initial_covers:
  assumes "rfc_initial_covers R I" and "t \<in> rhss (set R)"
  shows "t \<in> set I"
  using assms unfolding rfc_initial_covers_def
  by (auto simp: list_all_iff)

lemma rfc_term_accepted_with_tail_states_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and accepted: "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    and q: "q \<in> set qfin"
  shows "\<exists>qf\<in>ta_final (ta_of TA).
    qf \<in> ta_res (ta_of TA)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  from accepted q have nonempty:
    "\<not> rs.isEmpty (rs.inter (ta_final_impl TA)
      (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))))"
    unfolding rfc_term_accepted_with_tail_states_impl_def
    by (auto simp: list_all_iff)
  show ?thesis
    using nonempty
    by (auto simp: rs.correct ta_final ta_res_impl)
qed

lemma rfc_initial_accepted_with_tail_states_impl:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and accepted: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TA qfin I"
    and t: "t \<in> set I"
    and q: "q \<in> set qfin"
  shows "\<exists>qf\<in>ta_final (ta_of TA).
    qf \<in> ta_res (ta_of TA)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from accepted t have
    "rfc_term_accepted_with_tail_states_impl TYPE('f) TA qfin t"
    unfolding rfc_initial_accepted_with_tail_states_impl_def
    by (auto simp: list_all_iff)
  then show ?thesis
    by (rule rfc_term_accepted_with_tail_states_impl[OF inv _ q])
qed

lemma rfc_word_reaches_impl_sound:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and reach: "rfc_word_reaches_impl TA q w p"
  shows "p \<in> ta_res (ta_of TA)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term w ''x'')))"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
    using reach unfolding rfc_word_reaches_impl_def
    by (simp add: ta_res_impl rs.correct)
qed

lemma rfc_word_reaches_impl_complete:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and reach: "p \<in> ta_res (ta_of TA)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term w ''x'')))"
  shows "rfc_word_reaches_impl TA q w p"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
    using reach unfolding rfc_word_reaches_impl_def
    by (simp add: ta_res_impl rs.correct)
qed

lemma rfc_rule_automaton_closed_implD:
  assumes closed: "rfc_rule_automaton_closed_impl TA qs lr"
    and words: "rfc_rule_words lr = Some (lw,rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and q: "q \<in> set qs" and m: "m \<in> set qs" and p: "p \<in> set qs"
    and suffix: "rfc_word_reaches_impl TA q (drop i lw) m"
    and prefix: "rfc_word_reaches_impl TA m (take i lw) p"
  shows "rfc_word_reaches_impl TA q rw p"
  using assms unfolding rfc_rule_automaton_closed_impl_def
  by (auto simp: list_all_iff Let_def)

fun
  rfc_word_res_impl ::
    "(('f \<times> nat) \<times> nat,
      ('q :: linorder,'f :: linorder \<times> nat)ta_rule_impl list)rm \<Rightarrow>
      ('q \<Rightarrow> 'q rs) \<Rightarrow> 'q \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'q rs"
where
  "rfc_word_res_impl TA eps q h [] = eps q"
| "rfc_word_res_impl TA eps q h (f # fs) =
    (let rec = rfc_word_res_impl TA eps q h fs;
         rules = rm_set_lookup TA ((f,h),1);
         arules = filter (\<lambda>rule.
           rs.memb (r_lhs_states_impl rule ! 0) rec) rules
     in rs_Union (map rqss_impl arules))"

lemma rfc_word_res_impl_eq[simp]:
  fixes w :: "('f :: linorder) list"
  shows "rfc_word_res_impl TA eps q h w =
    ta_res_impl TA eps
      (map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w ''x'')))"
  by (induct w) (simp_all add: Let_def)

fun
  rfc_native_word_res_impl ::
    "(('f \<times> nat) \<times> nat,
      ('q :: linorder,'f :: linorder \<times> nat)ta_rule_impl list)rm \<Rightarrow>
      ('q \<Rightarrow> 'q rs) \<Rightarrow> 'q \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'q rs"
where
  "rfc_native_word_res_impl TA eps q h [] = rs.from_list [q]"
| "rfc_native_word_res_impl TA eps q h (f # fs) =
    (let rec0 = rfc_native_word_res_impl TA eps q h fs;
         rec = (if fs = [] then rec0
                else rs_Union (map eps (rs.to_list rec0)));
         rules = rm_set_lookup TA ((f,h),1);
         arules = filter (\<lambda>rule.
           rs.memb (r_lhs_states_impl rule ! 0) rec) rules
     in rs.from_list (map r_rhs_impl arules))"

text \<open>
The native Matchbox evaluator takes epsilon transitions strictly between
letters.  In particular, neither the supplied tail state nor the result after
the outermost letter is epsilon-closed.  This differs intentionally from
term-automaton evaluation and is the boundary convention used by the barren
and merge constructions.
\<close>

lemma rfc_native_word_res_impl_Nil[simp]:
  "rs.\<alpha> (rfc_native_word_res_impl TA eps q h []) = {q}"
  by (simp add: rs.correct)

lemma rfc_native_word_res_impl_singleton:
  "rfc_native_word_res_impl TA eps q h [f] =
    (let rules = rm_set_lookup TA ((f,h),1);
         arules = filter (\<lambda>rule.
           r_lhs_states_impl rule ! 0 = q) rules
     in rs.from_list (map r_rhs_impl arules))"
  by (auto simp: Let_def rs.correct)

fun
  rfc_native_labeled_word_res_impl ::
    "(('f \<times> nat) \<times> nat,
      ('q :: linorder,'f :: linorder \<times> nat)ta_rule_impl list)rm \<Rightarrow>
      ('q \<Rightarrow> 'q rs) \<Rightarrow> 'q \<Rightarrow> ('f \<times> nat) list \<Rightarrow> 'q rs"
where
  "rfc_native_labeled_word_res_impl TA eps q [] = rs.from_list [q]"
| "rfc_native_labeled_word_res_impl TA eps q (fh # fhs) =
    (let rec0 = rfc_native_labeled_word_res_impl TA eps q fhs;
         rec = (if fhs = [] then rec0
                else rs_Union (map eps (rs.to_list rec0)));
         rules = rm_set_lookup TA (fh,1);
         arules = filter (\<lambda>rule.
           rs.memb (r_lhs_states_impl rule ! 0) rec) rules
     in rs.from_list (map r_rhs_impl arules))"

lemma rfc_native_labeled_word_res_impl_uniform:
  "rfc_native_labeled_word_res_impl TA eps q (map (\<lambda>f. (f,h)) w) =
    rfc_native_word_res_impl TA eps q h w"
  by (induct w) (simp_all add: Let_def)

fun
  rfc_native_labeled_word_res ::
    "('q,('f \<times> nat))ta \<Rightarrow> 'q \<Rightarrow> ('f \<times> nat) list \<Rightarrow> 'q set"
where
  "rfc_native_labeled_word_res TA q [] = {q}"
| "rfc_native_labeled_word_res TA q (fh # fhs) =
    (let rec0 = rfc_native_labeled_word_res TA q fhs;
         rec = (if fhs = [] then rec0 else (ta_eps TA)\<^sup>* `` rec0)
     in {p. \<exists>a\<in>rec. (fh [a] \<rightarrow> p) \<in> ta_rules TA})"

lemma rtrancl_image_idem:
  "R\<^sup>* `` (R\<^sup>* `` A) = R\<^sup>* `` A"
  by (auto dest: rtrancl_trans)

lemma rfc_native_labeled_word_res_append:
  assumes xs: "xs \<noteq> []" and ys: "ys \<noteq> []"
  shows "p \<in> rfc_native_labeled_word_res TA q (xs @ ys) \<longleftrightarrow>
    (\<exists>m\<in>(ta_eps TA)\<^sup>* `` rfc_native_labeled_word_res TA q ys.
      p \<in> rfc_native_labeled_word_res TA m xs)"
  using xs ys
proof (induct xs arbitrary: p q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True
    with Cons.prems show ?thesis
      by (auto simp: Let_def)
  next
    case False
    have tail_ne: "xs @ ys \<noteq> []"
      using False by simp
    have ih: "\<And>z r. r \<in> rfc_native_labeled_word_res TA z (xs @ ys) \<longleftrightarrow>
      (\<exists>m\<in>(ta_eps TA)\<^sup>* `` rfc_native_labeled_word_res TA z ys.
        r \<in> rfc_native_labeled_word_res TA m xs)"
      using Cons.hyps[OF False Cons.prems(2)] .
    show ?thesis
    proof
      assume left: "p \<in> rfc_native_labeled_word_res TA q
        ((x # xs) @ ys)"
      from left obtain a xa where
        rule: "(x [a] \<rightarrow> p) \<in> ta_rules TA"
        and eps: "(xa,a) \<in> (ta_eps TA)\<^sup>*"
        and xa: "xa \<in> rfc_native_labeled_word_res TA q (xs @ ys)"
        using False tail_ne
        by (auto simp: Let_def)
      from ih[of xa q] xa obtain m where
        m: "m \<in> (ta_eps TA)\<^sup>* ``
          rfc_native_labeled_word_res TA q ys"
        and xa_m: "xa \<in> rfc_native_labeled_word_res TA m xs"
        by auto
      have "p \<in> rfc_native_labeled_word_res TA m (x # xs)"
        using rule eps xa_m False
        by (auto simp: Let_def)
      with m show "\<exists>m\<in>(ta_eps TA)\<^sup>* ``
          rfc_native_labeled_word_res TA q ys.
        p \<in> rfc_native_labeled_word_res TA m (x # xs)"
        by blast
    next
      assume right: "\<exists>m\<in>(ta_eps TA)\<^sup>* ``
          rfc_native_labeled_word_res TA q ys.
        p \<in> rfc_native_labeled_word_res TA m (x # xs)"
      then obtain m where
        m: "m \<in> (ta_eps TA)\<^sup>* ``
          rfc_native_labeled_word_res TA q ys"
        and p_m: "p \<in> rfc_native_labeled_word_res TA m (x # xs)"
        by blast
      from p_m obtain a xa where
        rule: "(x [a] \<rightarrow> p) \<in> ta_rules TA"
        and eps: "(xa,a) \<in> (ta_eps TA)\<^sup>*"
        and xa_m: "xa \<in> rfc_native_labeled_word_res TA m xs"
        using False by (auto simp: Let_def)
      have xa: "xa \<in> rfc_native_labeled_word_res TA q (xs @ ys)"
        using ih[of xa q] m xa_m by auto
      show "p \<in> rfc_native_labeled_word_res TA q ((x # xs) @ ys)"
        using rule eps xa False tail_ne
        by (auto simp: Let_def)
    qed
  qed
qed

lemma rfc_native_labeled_word_res_ta_res:
  fixes TA :: "('q,('f \<times> nat))ta"
    and fhs :: "('f \<times> nat) list"
  shows "p \<in> ta_res TA
      (map_vars_term (\<lambda>_. q) (rfc_word_term fhs ''x'')) \<longleftrightarrow>
    (\<exists>q0\<in>(ta_eps TA)\<^sup>* `` {q}.
      \<exists>p0\<in>rfc_native_labeled_word_res TA q0 fhs.
        (p0,p) \<in> (ta_eps TA)\<^sup>*)"
proof (induct fhs arbitrary: p)
  case Nil
  then show ?case
    by (auto dest: rtrancl_trans)
next
  case (Cons fh fhs)
  show ?case
  proof (cases "fhs = []")
    case True
    show ?thesis
    proof
      assume left: "p \<in> ta_res TA
        (map_vars_term (\<lambda>_. q) (rfc_word_term (fh # fhs) ''x''))"
      from left True obtain qa qs where
        rule: "(fh qs \<rightarrow> qa) \<in> ta_rules TA"
        and final: "(qa,p) \<in> (ta_eps TA)\<^sup>*"
        and len: "length qs = 1"
        and arg: "(q,qs ! 0) \<in> (ta_eps TA)\<^sup>*"
        by auto
      from len obtain a where qs: "qs = [a]"
        by (auto simp: length_Suc_conv)
      show "\<exists>q0\<in>(ta_eps TA)\<^sup>* `` {q}.
          \<exists>p0\<in>rfc_native_labeled_word_res TA q0 (fh # fhs).
            (p0,p) \<in> (ta_eps TA)\<^sup>*"
        using rule final arg qs True
        by (rule_tac x=a in bexI, auto simp: Let_def)
    next
      assume right: "\<exists>q0\<in>(ta_eps TA)\<^sup>* `` {q}.
          \<exists>p0\<in>rfc_native_labeled_word_res TA q0 (fh # fhs).
            (p0,p) \<in> (ta_eps TA)\<^sup>*"
      then obtain q0 p0 where
        q0: "(q,q0) \<in> (ta_eps TA)\<^sup>*"
        and p0: "p0 \<in> rfc_native_labeled_word_res TA q0 (fh # fhs)"
        and final: "(p0,p) \<in> (ta_eps TA)\<^sup>*"
        by auto
      from p0 True have rule: "(fh [q0] \<rightarrow> p0) \<in> ta_rules TA"
        by (auto simp: Let_def)
      show "p \<in> ta_res TA
          (map_vars_term (\<lambda>_. q) (rfc_word_term (fh # fhs) ''x''))"
        using rule q0 final True
        apply simp
        apply (rule exI[of _ p0])
        apply (rule exI[of _ "[q0]"])
        apply simp
        done
    qed
  next
    case False
    show ?thesis
    proof
      assume left: "p \<in> ta_res TA
        (map_vars_term (\<lambda>_. q) (rfc_word_term (fh # fhs) ''x''))"
      from left obtain qa qs where
        rule: "(fh qs \<rightarrow> qa) \<in> ta_rules TA"
        and final: "(qa,p) \<in> (ta_eps TA)\<^sup>*"
        and len: "length qs = 1"
        and arg: "qs ! 0 \<in> ta_res TA
          (map_vars_term (\<lambda>_. q) (rfc_word_term fhs ''x''))"
        by auto
      from len obtain a where qs: "qs = [a]"
        by (auto simp: length_Suc_conv)
      from Cons.hyps[of a] arg obtain q0 p0 where
        q0: "(q,q0) \<in> (ta_eps TA)\<^sup>*"
        and p0: "p0 \<in> rfc_native_labeled_word_res TA q0 fhs"
        and eps: "(p0,a) \<in> (ta_eps TA)\<^sup>*"
        using qs by auto
      have native: "qa \<in> rfc_native_labeled_word_res TA q0 (fh # fhs)"
        using rule p0 eps qs False by (auto simp: Let_def)
      show "\<exists>q0\<in>(ta_eps TA)\<^sup>* `` {q}.
          \<exists>p0\<in>rfc_native_labeled_word_res TA q0 (fh # fhs).
            (p0,p) \<in> (ta_eps TA)\<^sup>*"
        using q0 native final by auto
    next
      assume right: "\<exists>q0\<in>(ta_eps TA)\<^sup>* `` {q}.
          \<exists>p0\<in>rfc_native_labeled_word_res TA q0 (fh # fhs).
            (p0,p) \<in> (ta_eps TA)\<^sup>*"
      then obtain q0 p0 where
        q0: "(q,q0) \<in> (ta_eps TA)\<^sup>*"
        and p0: "p0 \<in> rfc_native_labeled_word_res TA q0 (fh # fhs)"
        and final: "(p0,p) \<in> (ta_eps TA)\<^sup>*"
        by auto
      from p0 obtain a a0 where
        rule: "(fh [a] \<rightarrow> p0) \<in> ta_rules TA"
        and eps: "(a0,a) \<in> (ta_eps TA)\<^sup>*"
        and a0: "a0 \<in> rfc_native_labeled_word_res TA q0 fhs"
        using False by (auto simp: Let_def)
      have arg: "a \<in> ta_res TA
          (map_vars_term (\<lambda>_. q) (rfc_word_term fhs ''x''))"
        using Cons.hyps[of a] q0 a0 eps by auto
      show "p \<in> ta_res TA
          (map_vars_term (\<lambda>_. q) (rfc_word_term (fh # fhs) ''x''))"
        using rule arg final
        apply simp
        apply (rule exI[of _ p0])
        apply (rule exI[of _ "[a]"])
        apply simp
        done
    qed
  qed
qed

lemma rfc_native_labeled_word_res_states:
  fixes TA :: "('q,('f \<times> nat))ta"
  assumes ne: "fhs \<noteq> []"
    and p: "p \<in> rfc_native_labeled_word_res TA q fhs"
  shows "q \<in> ta_states TA \<and> p \<in> ta_states TA"
  using ne p
proof (induct fhs arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons fh fhs)
  show ?case
  proof (cases "fhs = []")
    case True
    from Cons.prems True obtain rule where
      rule: "(fh [q] \<rightarrow> p) \<in> ta_rules TA"
      by (auto simp: Let_def)
    then show ?thesis
      using r_rhs_states[OF rule]
      unfolding ta_states_def r_states_def by force
  next
    case False
    from Cons.prems obtain a0 a where
      a0: "a0 \<in> rfc_native_labeled_word_res TA q fhs"
      and eps: "(a0,a) \<in> (ta_eps TA)\<^sup>*"
      and rule: "(fh [a] \<rightarrow> p) \<in> ta_rules TA"
      using False by (auto simp: Let_def)
    from Cons.hyps[OF False a0] have q_state: "q \<in> ta_states TA"
      and a0_state: "a0 \<in> ta_states TA"
      by auto
    have a_state: "a \<in> ta_states TA"
      by (rule ta_eps_ta_states[OF a0_state eps])
    have p_state: "p \<in> ta_states TA"
      by (rule r_rhs_states[OF rule])
    from q_state p_state show ?thesis by auto
  qed
qed

fun
  rfc_labeled_height_vectors :: "nat \<Rightarrow> 'f list \<Rightarrow> ('f \<times> nat) list list"
where
  "rfc_labeled_height_vectors c [] = [[]]"
| "rfc_labeled_height_vectors c (f # fs) =
    concat (map (\<lambda>h.
      map (Cons (f,h)) (rfc_labeled_height_vectors c fs))
      [0..<Suc c])"

lemma rfc_labeled_height_vectors_length:
  assumes "fhs \<in> set (rfc_labeled_height_vectors c fs)"
  shows "length fhs = length fs"
  using assms by (induct fs arbitrary: fhs) auto

lemma rfc_labeled_height_vectors_fst:
  assumes "fhs \<in> set (rfc_labeled_height_vectors c fs)"
  shows "map fst fhs = fs"
  using assms by (induct fs arbitrary: fhs) auto

lemma rfc_labeled_height_vectors_bound:
  assumes "fhs \<in> set (rfc_labeled_height_vectors c fs)"
    and "fh \<in> set fhs"
  shows "snd fh \<le> c"
  using assms by (induct fs arbitrary: fhs) auto

lemma rfc_labeled_height_vectors_complete:
  assumes bases: "map fst fhs = fs"
    and bound: "\<And>fh. fh \<in> set fhs \<Longrightarrow> snd fh \<le> c"
  shows "fhs \<in> set (rfc_labeled_height_vectors c fs)"
  using bases bound
proof (induct fs arbitrary: fhs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  from Cons.prems(1) have "fhs \<noteq> []"
    by auto
  then obtain fh fhs' where fhs: "fhs = fh # fhs'"
    by (cases fhs) auto
  from Cons.prems fhs have fst: "fst fh = f"
    and tail: "map fst fhs' = fs"
    and h: "snd fh \<le> c"
    and tail_bound: "\<And>x. x \<in> set fhs' \<Longrightarrow> snd x \<le> c"
    by auto
  obtain h' where fh: "fh = (f,h')"
    using fst by (cases fh) auto
  have h'_range: "h' \<in> set [0..<Suc c]"
    using h unfolding fh by auto
  have tail_mem: "fhs' \<in> set (rfc_labeled_height_vectors c fs)"
    by (rule Cons.hyps[OF tail tail_bound])
  show ?case
    unfolding fhs fh
    using h'_range tail_mem by auto
qed

definition
  rfc_labeled_min_height :: "('f \<times> nat) list \<Rightarrow> nat"
where
  "rfc_labeled_min_height fhs \<equiv>
    min_list (map snd fhs)"

lemma rfc_labeled_min_height_min_list:
  assumes "fhs \<noteq> []"
  shows "rfc_labeled_min_height fhs = min_list (map snd fhs)"
  using assms
  by (simp add: rfc_labeled_min_height_def)

lemma funs_term_list_rfc_word_term[simp]:
  "funs_term_list (rfc_word_term w x) = w"
  by (induct w) (simp_all add: funs_term_list.simps)

lemma funas_term_rfc_word_term:
  "funas_term (rfc_word_term w x) = (\<lambda>f. (f,1)) ` set w"
  by (induct w) auto

lemma lift_term_rfc_word_term:
  fixes w :: "'f list"
  shows "lift_term h (rfc_word_term w x) =
    rfc_word_term (map (\<lambda>f. (f,h)) w) x"
  by (induct w) auto

lemma base_term_rfc_word_termE:
  fixes l :: "('f \<times> nat,string)term"
  assumes base: "base_term l = rfc_word_term w x"
  obtains fhs where
    "l = rfc_word_term fhs x"
    "map fst fhs = w"
proof (atomize_elim, insert base, induct w arbitrary: l)
  case Nil
  then show ?case
    by (cases l) auto
next
  case (Cons f fs)
  then obtain fh ts where l: "l = Fun fh ts"
    by (cases l) auto
  from Cons.prems[unfolded l] obtain t where
    ts: "ts = [t]" and base_fh: "fst fh = f"
      and base_t: "base_term t = rfc_word_term fs x"
    by (cases fh) auto
  from Cons.hyps[OF base_t] obtain fhs where
    t: "t = rfc_word_term fhs x" and bases: "map fst fhs = fs"
    by auto
  show ?case
    using l ts base_fh t bases
    by (rule_tac x="fh # fhs" in exI) auto
qed

fun
  rfc_native_word_res ::
    "('q,'f \<times> nat)ta \<Rightarrow> 'q \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'q set"
where
  "rfc_native_word_res TA q h [] = {q}"
| "rfc_native_word_res TA q h (f # fs) =
    (let rec0 = rfc_native_word_res TA q h fs;
         rec = (if fs = [] then rec0 else (ta_eps TA)\<^sup>* `` rec0)
     in {p. \<exists>a\<in>rec. ((f,h) [a] \<rightarrow> p) \<in> ta_rules TA})"

lemma rfc_native_labeled_word_res_uniform:
  "rfc_native_labeled_word_res TA q (map (\<lambda>f. (f,h)) w) =
    rfc_native_word_res TA q h w"
  by (induct w) (simp_all add: Let_def)

lemma rfc_native_labeled_word_res_impl_eq:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
  shows "rs.\<alpha> (rfc_native_labeled_word_res_impl
      (ta_rules_impl TA) (ta_epss_impl TA) q fhs) =
    rfc_native_labeled_word_res (ta_of TA) q fhs"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
  proof (induct fhs)
    case Nil
    then show ?case by (simp add: rs.correct)
  next
    case (Cons fh fhs)
    let ?rec0 = "rfc_native_labeled_word_res_impl
      (ta_rules_impl TA) (ta_epss_impl TA) q fhs"
    let ?rec = "if fhs = [] then ?rec0
      else rs_Union (map (ta_epss_impl TA) (rs.to_list ?rec0))"
    have rec_alpha: "rs.\<alpha> ?rec =
      (if fhs = [] then rfc_native_labeled_word_res (ta_of TA) q fhs
       else (ta_eps (ta_of TA))\<^sup>* ``
         rfc_native_labeled_word_res (ta_of TA) q fhs)"
    proof (cases "fhs = []")
      case True
      then show ?thesis using Cons by simp
    next
      case False
      then show ?thesis
        using Cons
        by (auto simp: rs.correct ta_epss)
    qed
    show ?case
    proof (rule set_eqI)
      fix p
      show "(p \<in> rs.\<alpha> (rfc_native_labeled_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q (fh # fhs))) =
        (p \<in> rfc_native_labeled_word_res (ta_of TA) q (fh # fhs))"
      proof
        assume left: "p \<in> rs.\<alpha> (rfc_native_labeled_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q (fh # fhs))"
        then obtain rule where
          rule: "rule \<in> set (ta_rm_set_lookup (fh,1))"
          and arg: "r_lhs_states_impl rule ! 0 \<in>
            (if fhs = [] then rfc_native_labeled_word_res (ta_of TA) q fhs
             else (ta_eps (ta_of TA))\<^sup>* ``
               rfc_native_labeled_word_res (ta_of TA) q fhs)"
          and p: "p = r_rhs_impl rule"
          using left rec_alpha
          by (auto simp: Let_def rs.correct)
        from rm_set_lookup1[OF rule] obtain qs p' qs' where
          id: "rule = TA_rule_impl fh qs p' qs'"
          and len: "1 = length qs"
          and abs_rule: "(fh qs \<rightarrow> p') \<in> ta_rules (ta_of TA)"
          by auto
        have lhs: "r_lhs_states_impl rule = qs"
          using id by simp
        from len obtain a where qs: "qs = [a]"
          by (cases qs) auto
        have a: "a = r_lhs_states_impl rule ! 0"
          using lhs qs by simp
        have p': "p' = p"
          using id p by simp
        have abs_rule': "(fh [r_lhs_states_impl rule ! 0] \<rightarrow> p)
            \<in> ta_rules (ta_of TA)"
          using abs_rule qs a p' by simp
        show "p \<in> rfc_native_labeled_word_res (ta_of TA) q (fh # fhs)"
          unfolding rfc_native_labeled_word_res.simps Let_def
          using arg abs_rule'
          by (simp only: mem_Collect_eq) blast
      next
        assume right: "p \<in> rfc_native_labeled_word_res
          (ta_of TA) q (fh # fhs)"
        then obtain a where
          arg: "a \<in> (if fhs = [] then
              rfc_native_labeled_word_res (ta_of TA) q fhs
            else (ta_eps (ta_of TA))\<^sup>* ``
              rfc_native_labeled_word_res (ta_of TA) q fhs)"
          and abs_rule: "(fh [a] \<rightarrow> p) \<in> ta_rules (ta_of TA)"
          by (auto simp: Let_def)
        let ?rule = "conv_ta_rule (ta_epss_impl TA) (fh [a] \<rightarrow> p)"
        have conv: "?rule \<in> conv_ta_rule (ta_epss_impl TA) `
            ta_rules (ta_of TA)"
          using abs_rule by blast
        have lookup0: "?rule \<in> set (ta_rm_set_lookup (r_sym_impl ?rule))"
          by (rule rm_set_lookup2[OF conv])
        have lookup: "?rule \<in> set (ta_rm_set_lookup (fh,1))"
          using lookup0 by simp
        have arg_impl: "a \<in> rs.\<alpha> ?rec"
          using arg rec_alpha by simp
        have selected: "?rule \<in>
            {rule \<in> set (ta_rm_set_lookup (fh,1)).
              r_lhs_states_impl rule ! 0 \<in> rs.\<alpha> ?rec}"
          using lookup arg_impl by simp
        have unfold: "rfc_native_labeled_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q (fh # fhs) =
          rs.from_list (map r_rhs_impl
            (filter (\<lambda>rule. rs.memb (r_lhs_states_impl rule ! 0) ?rec)
              (ta_rm_set_lookup (fh,1))))"
          by (simp only: rfc_native_labeled_word_res_impl.simps Let_def)
        have rhs: "r_rhs_impl ?rule = p"
          by simp
        show "p \<in> rs.\<alpha> (rfc_native_labeled_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q (fh # fhs))"
          unfolding unfold
          apply (simp only: rs.correct set_map set_filter mem_Collect_eq)
          apply (subst rhs[symmetric])
          apply (rule imageI)
          using selected
          apply (simp add: rs.correct)
          done
      qed
    qed
  qed
qed

lemma rfc_native_word_res_impl_eq:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
  shows "rs.\<alpha> (rfc_native_word_res_impl
      (ta_rules_impl TA) (ta_epss_impl TA) q h w) =
    rfc_native_word_res (ta_of TA) q h w"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
  proof (induct w)
    case Nil
    then show ?case by (simp add: rs.correct)
  next
    case (Cons f fs)
    let ?rec0 = "rfc_native_word_res_impl
      (ta_rules_impl TA) (ta_epss_impl TA) q h fs"
    let ?rec = "if fs = [] then ?rec0
      else rs_Union (map (ta_epss_impl TA) (rs.to_list ?rec0))"
    have rec_alpha: "rs.\<alpha> ?rec =
      (if fs = [] then rfc_native_word_res (ta_of TA) q h fs
       else (ta_eps (ta_of TA))\<^sup>* ``
         rfc_native_word_res (ta_of TA) q h fs)"
    proof (cases "fs = []")
      case True
      then show ?thesis using Cons by simp
    next
      case False
      then show ?thesis
        using Cons
        by (auto simp: rs.correct ta_epss)
    qed
    show ?case
    proof (rule set_eqI)
      fix p
      show "(p \<in> rs.\<alpha> (rfc_native_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q h (f # fs))) =
        (p \<in> rfc_native_word_res (ta_of TA) q h (f # fs))"
      proof
        assume left: "p \<in> rs.\<alpha> (rfc_native_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q h (f # fs))"
        then obtain rule where
          rule: "rule \<in> set (ta_rm_set_lookup ((f,h),1))"
          and arg: "r_lhs_states_impl rule ! 0 \<in>
            (if fs = [] then rfc_native_word_res (ta_of TA) q h fs
             else (ta_eps (ta_of TA))\<^sup>* ``
               rfc_native_word_res (ta_of TA) q h fs)"
          and p: "p = r_rhs_impl rule"
          using left rec_alpha
          by (auto simp: Let_def rs.correct)
        from rm_set_lookup1[OF rule] obtain qs p' qs' where
          id: "rule = TA_rule_impl (f,h) qs p' qs'"
          and len: "1 = length qs"
          and abs_rule: "((f,h) qs \<rightarrow> p') \<in> ta_rules (ta_of TA)"
          by auto
        have lhs: "r_lhs_states_impl rule = qs"
          using id by simp
        from len obtain a where qs: "qs = [a]"
          by (cases qs) auto
        have a: "a = r_lhs_states_impl rule ! 0"
          using lhs qs by simp
        have p': "p' = p"
          using id p by simp
        have abs_rule': "((f,h) [r_lhs_states_impl rule ! 0] \<rightarrow> p)
            \<in> ta_rules (ta_of TA)"
          using abs_rule qs a p' by simp
        show "p \<in> rfc_native_word_res (ta_of TA) q h (f # fs)"
          unfolding rfc_native_word_res.simps Let_def
          using arg abs_rule'
          by (simp only: mem_Collect_eq) blast
      next
        assume right: "p \<in> rfc_native_word_res (ta_of TA) q h (f # fs)"
        then obtain a where
          arg: "a \<in> (if fs = [] then rfc_native_word_res (ta_of TA) q h fs
            else (ta_eps (ta_of TA))\<^sup>* ``
              rfc_native_word_res (ta_of TA) q h fs)"
          and abs_rule: "((f,h) [a] \<rightarrow> p) \<in> ta_rules (ta_of TA)"
          by (auto simp: Let_def)
        let ?rule = "conv_ta_rule (ta_epss_impl TA) ((f,h) [a] \<rightarrow> p)"
        have conv: "?rule \<in> conv_ta_rule (ta_epss_impl TA) `
            ta_rules (ta_of TA)"
          using abs_rule by blast
        have lookup0: "?rule \<in> set (ta_rm_set_lookup (r_sym_impl ?rule))"
          by (rule rm_set_lookup2[OF conv])
        have lookup: "?rule \<in> set (ta_rm_set_lookup ((f,h),1))"
          using lookup0 by simp
        have arg_impl: "a \<in> rs.\<alpha> ?rec"
          using arg rec_alpha by simp
        have selected: "?rule \<in>
            {rule \<in> set (ta_rm_set_lookup ((f,h),1)).
              r_lhs_states_impl rule ! 0 \<in> rs.\<alpha> ?rec}"
          using lookup arg_impl by simp
        have unfold: "rfc_native_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q h (f # fs) =
          rs.from_list (map r_rhs_impl
            (filter (\<lambda>rule. rs.memb (r_lhs_states_impl rule ! 0) ?rec)
              (ta_rm_set_lookup ((f,h),1))))"
          by (simp only: rfc_native_word_res_impl.simps Let_def)
        have rhs: "r_rhs_impl ?rule = p"
          by simp
        show "p \<in> rs.\<alpha> (rfc_native_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q h (f # fs))"
          unfolding unfold
          apply (simp only: rs.correct set_map set_filter mem_Collect_eq)
          apply (subst rhs[symmetric])
          apply (rule imageI)
          using selected
          apply (simp add: rs.correct)
          done
      qed
    qed
  qed
qed

definition
  rfc_unary_rule_index_impl ::
    "('q :: linorder,'f)ta_rule_impl list \<Rightarrow>
      ('q,('q,'f)ta_rule_impl list)RBT.rbt"
where
  "rfc_unary_rule_index_impl rules \<equiv>
    elem_list_to_rm (\<lambda>rule. r_lhs_states_impl rule ! 0) rules"

definition
  rfc_word_indexed_step_impl ::
    "('q :: linorder,'f)ta_rule_impl list \<Rightarrow> 'q rs \<Rightarrow> 'q rs"
where
  "rfc_word_indexed_step_impl rules rec \<equiv>
    (let idx = rfc_unary_rule_index_impl rules in
      rs_Union (map (\<lambda>p.
        rs_Union (map rqss_impl (rm_set_lookup idx p)))
        (rs.to_list rec)))"

lemma rfc_word_indexed_step_impl:
  "rs.\<alpha> (rfc_word_indexed_step_impl rules rec) =
    rs.\<alpha> (rs_Union (map rqss_impl
      (filter (\<lambda>rule.
        rs.memb (r_lhs_states_impl rule ! 0) rec) rules)))"
  unfolding rfc_word_indexed_step_impl_def rfc_unary_rule_index_impl_def
  by (auto simp: rs.correct elem_list_to_rm.rm_set_lookup)

definition
  rfc_word_scan_step_impl ::
    "('q :: linorder,'f)ta_rule_impl list \<Rightarrow> 'q rs \<Rightarrow> 'q rs"
where
  "rfc_word_scan_step_impl rules rec \<equiv>
    rs_Union (map rqss_impl
      (filter (\<lambda>rule.
        rs.memb (r_lhs_states_impl rule ! 0) rec) rules))"

lemma rfc_word_indexed_scan_step_impl:
  "rs.\<alpha> (rfc_word_indexed_step_impl rules rec) =
    rs.\<alpha> (rfc_word_scan_step_impl rules rec)"
  unfolding rfc_word_scan_step_impl_def
  by (rule rfc_word_indexed_step_impl)

lemma rfc_word_scan_step_impl_cong:
  assumes "rs.\<alpha> rec = rs.\<alpha> rec'"
  shows "rs.\<alpha> (rfc_word_scan_step_impl rules rec) =
    rs.\<alpha> (rfc_word_scan_step_impl rules rec')"
  using assms
  unfolding rfc_word_scan_step_impl_def
  by (auto simp: rs.correct)

lemma map_rfc_word_indexed_scan_step_impl:
  assumes "map rs.\<alpha> recs = map rs.\<alpha> recs'"
  shows
    "map rs.\<alpha> (map (rfc_word_indexed_step_impl rules) recs) =
      map rs.\<alpha> (map (rfc_word_scan_step_impl rules) recs')"
  using assms
proof (induct recs arbitrary: recs')
  case Nil
  then show ?case by simp
next
  case (Cons rec recs)
  then obtain rec' recs'' where recs':
    "recs' = rec' # recs''"
    by (cases recs') auto
  with Cons.prems have head:
    "rs.\<alpha> rec = rs.\<alpha> rec'"
    and tail:
    "map rs.\<alpha> recs = map rs.\<alpha> recs''"
    by auto
  have indexed:
    "rs.\<alpha> (rfc_word_indexed_step_impl rules rec) =
      rs.\<alpha> (rfc_word_scan_step_impl rules rec')"
    using rfc_word_indexed_scan_step_impl[of rules rec]
      rfc_word_scan_step_impl_cong[OF head, of rules]
    by simp
  show ?case
    unfolding recs'
    using indexed Cons.hyps[OF tail]
    by simp
qed

fun
  rfc_word_results_impl ::
    "(('f \<times> nat) \<times> nat,
      ('q :: linorder,'f :: linorder \<times> nat)ta_rule_impl list)rm \<Rightarrow>
      ('q \<Rightarrow> 'q rs) \<Rightarrow> nat \<Rightarrow> 'f list \<Rightarrow> 'q list \<Rightarrow> 'q rs list"
where
  "rfc_word_results_impl TA eps h [] qs = map eps qs"
| "rfc_word_results_impl TA eps h (f # fs) qs =
    (let recs = rfc_word_results_impl TA eps h fs qs;
         rules = rm_set_lookup TA ((f,h),1)
     in map (rfc_word_indexed_step_impl rules) recs)"

lemma rfc_word_results_impl_eq:
  "map rs.\<alpha> (rfc_word_results_impl TA eps h w qs) =
    map (\<lambda>q. rs.\<alpha> (rfc_word_res_impl TA eps q h w)) qs"
proof (induct w arbitrary: qs)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  let ?recs = "rfc_word_results_impl TA eps h fs qs"
  let ?old = "map (\<lambda>q. rfc_word_res_impl TA eps q h fs) qs"
  let ?rules = "rm_set_lookup TA ((f,h),1)"
  have alpha:
    "map rs.\<alpha> ?recs = map rs.\<alpha> ?old"
    using Cons.hyps[of qs]
    by simp
  have step:
    "map rs.\<alpha> (map (rfc_word_indexed_step_impl ?rules) ?recs) =
      map rs.\<alpha> (map (rfc_word_scan_step_impl ?rules) ?old)"
    by (rule map_rfc_word_indexed_scan_step_impl[OF alpha])
  show ?case
    using step
    by (simp add: Let_def rfc_word_scan_step_impl_def)
qed

lemma rel_checker_some_none:
  "(rel_checker (Some_Relation rel) lhs rhs = None) =
    (\<forall>l \<in> rs.\<alpha> lhs. \<exists>r \<in> rs.\<alpha> rhs. (l,r) \<in> set rel)"
proof -
  let ?check = "check_allm
    (\<lambda>l. check (\<exists>r \<in> set (rs.to_list rhs). (l,r) \<in> set rel) l)
    (rs.to_list lhs)"
  have "(rel_checker (Some_Relation rel) lhs rhs = None) = isOK ?check"
    by (cases ?check) auto
  also have "\<dots> =
    (\<forall>l \<in> rs.\<alpha> lhs. \<exists>r \<in> rs.\<alpha> rhs. (l,r) \<in> set rel)"
    by (simp add: isOK_check_allm rs.correct)
  finally show ?thesis .
qed

lemma rel_checker_alpha_cong:
  assumes "rs.\<alpha> lhs = rs.\<alpha> lhs'"
    and "rs.\<alpha> rhs = rs.\<alpha> rhs'"
  shows "(rel_checker rel lhs rhs = None) =
    (rel_checker rel lhs' rhs' = None)"
proof (cases rel)
  case (Some_Relation relation)
  then show ?thesis
    using assms
    by (simp only: rel_checker_some_none)
qed (use assms in \<open>auto simp: rs_\<alpha>_to_RBT_keys\<close>)

lemma list_all2_rel_checker_alpha_cong:
  assumes "map rs.\<alpha> xs = map rs.\<alpha> xs'"
    and "map rs.\<alpha> ys = map rs.\<alpha> ys'"
  shows "list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None) xs ys =
    list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None) xs' ys'"
  using assms
proof (induct xs arbitrary: ys xs' ys')
  case Nil
  then show ?case
    by (cases xs'; cases ys; cases ys') auto
next
  case (Cons lhs xs)
  then obtain lhs' xs'' where lhs':
    "xs' = lhs' # xs''"
    by (cases xs') auto
  show ?case
  proof (cases ys)
    case Nil
    with Cons.prems lhs' show ?thesis by simp
  next
    case (Cons rhs ys'')
    then obtain rhs' ys''' where rhs':
      "ys' = rhs' # ys'''"
      using Cons.prems by (cases ys') auto
    from Cons.prems lhs' Cons rhs' have heads:
      "rs.\<alpha> lhs = rs.\<alpha> lhs'"
      "rs.\<alpha> rhs = rs.\<alpha> rhs'"
      and tails:
      "map rs.\<alpha> xs = map rs.\<alpha> xs''"
      "map rs.\<alpha> ys'' = map rs.\<alpha> ys'''"
      by auto
    show ?thesis
      unfolding lhs' Cons rhs'
      using rel_checker_alpha_cong[OF heads]
        Cons.hyps[OF tails]
      by simp
  qed
qed

lemma list_all2_map_same:
  "list_all2 P (map f xs) (map g xs) =
    list_all (\<lambda>x. P (f x) (g x)) xs"
  by (induct xs) simp_all

lemma list_all_map_same:
  "list_all P (map f xs) = list_all (\<lambda>x. P (f x)) xs"
  by (induct xs) simp_all

lemma list_all_alpha_cong:
  assumes "map rs.\<alpha> xs = map rs.\<alpha> ys"
    and "\<And>x y. rs.\<alpha> x = rs.\<alpha> y \<Longrightarrow> P x = P y"
  shows "list_all P xs = list_all P ys"
  using assms(1)
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by (cases ys) simp_all
next
  case (Cons x xs)
  then obtain y ys' where ys: "ys = y # ys'"
    by (cases ys) auto
  with Cons.prems have head: "rs.\<alpha> x = rs.\<alpha> y"
    and tail: "map rs.\<alpha> xs = map rs.\<alpha> ys'"
    by auto
  show ?case
    unfolding ys
    using assms(2)[OF head] Cons.hyps[OF tail]
    by simp
qed

lemma rfc_word_results_rel_checker:
  "list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
      (rfc_word_results_impl TA eps h lw qs)
      (rfc_word_results_impl TA eps h rw qs) =
    list_all (\<lambda>q.
      rel_checker rel
        (rfc_word_res_impl TA eps q h lw)
        (rfc_word_res_impl TA eps q h rw) = None) qs"
proof -
  have lhs:
    "map rs.\<alpha> (rfc_word_results_impl TA eps h lw qs) =
      map rs.\<alpha> (map (\<lambda>q. rfc_word_res_impl TA eps q h lw) qs)"
    using rfc_word_results_impl_eq[of TA eps h lw qs]
    by simp
  have rhs:
    "map rs.\<alpha> (rfc_word_results_impl TA eps h rw qs) =
      map rs.\<alpha> (map (\<lambda>q. rfc_word_res_impl TA eps q h rw) qs)"
    using rfc_word_results_impl_eq[of TA eps h rw qs]
    by simp
  have "list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
      (rfc_word_results_impl TA eps h lw qs)
      (rfc_word_results_impl TA eps h rw qs) =
    list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
      (map (\<lambda>q. rfc_word_res_impl TA eps q h lw) qs)
      (map (\<lambda>q. rfc_word_res_impl TA eps q h rw) qs)"
    by (rule list_all2_rel_checker_alpha_cong[OF lhs rhs])
  then show ?thesis
    by (simp add: list_all2_map_same)
qed

definition
  rfc_word_reaches_height_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow> 'q \<Rightarrow> nat \<Rightarrow> ('f list) \<Rightarrow> 'q \<Rightarrow> bool"
where
  "rfc_word_reaches_height_impl TA q h w p \<equiv>
    rs.memb p
      (rfc_word_res_impl (ta_rules_impl TA) (ta_epss_impl TA) q h w)"

definition
  rfc_rule_has_top_redex_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow> 'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_has_top_redex_impl TA qs c lr \<equiv> (case rfc_rule_words lr of
      None \<Rightarrow> True
    | Some (lw, rw) \<Rightarrow>
        \<not> list_all (\<lambda>q.
          list_all (\<lambda>p. \<not> rfc_word_reaches_height_impl TA q c lw p) qs) qs)"

definition
  rfc_no_top_redex_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow> 'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_no_top_redex_impl TA qs c R \<equiv>
    list_all (\<lambda>lr. \<not> rfc_rule_has_top_redex_impl TA qs c lr) R"

definition
  rfc_rule_no_top_redex_fast_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_no_top_redex_fast_impl TA qs c lr \<equiv>
    (let qset = rs.from_list qs in
      case rfc_rule_words lr of
        None \<Rightarrow> False
      | Some (lw, rw) \<Rightarrow>
          list_all (\<lambda>q.
            rs.isEmpty (rs.inter qset
              (rfc_word_res_impl
                (ta_rules_impl TA) (ta_epss_impl TA) q c lw)))
            qs)"

definition
  rfc_no_top_redex_fast_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_no_top_redex_fast_impl TA qs c R \<equiv>
    list_all (rfc_rule_no_top_redex_fast_impl TA qs c) R"

definition
  rfc_rule_no_top_redex_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_no_top_redex_indexed_impl TA qs c lr \<equiv>
    (let qset = rs.from_list qs in
      case rfc_rule_words lr of
        None \<Rightarrow> False
      | Some (lw, rw) \<Rightarrow>
          list_all (\<lambda>res. rs.isEmpty (rs.inter qset res))
            (rfc_word_results_impl
              (ta_rules_impl TA) (ta_epss_impl TA) c lw qs))"

definition
  rfc_no_top_redex_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_no_top_redex_indexed_impl TA qs c R \<equiv>
    list_all (rfc_rule_no_top_redex_indexed_impl TA qs c) R"

lemma rfc_rule_no_top_redex_indexed_impl_eq:
  "rfc_rule_no_top_redex_indexed_impl TA qs c lr =
    rfc_rule_no_top_redex_fast_impl TA qs c lr"
proof (cases "rfc_rule_words lr")
  case None
  then show ?thesis
    by (simp add: rfc_rule_no_top_redex_indexed_impl_def
      rfc_rule_no_top_redex_fast_impl_def Let_def)
next
  case (Some words)
  then obtain lw rw where words: "words = (lw,rw)"
    by (cases words)
  let ?qset = "rs.from_list qs"
  let ?results = "rfc_word_results_impl
    (ta_rules_impl TA) (ta_epss_impl TA) c lw qs"
  let ?old = "map (\<lambda>q. rfc_word_res_impl
    (ta_rules_impl TA) (ta_epss_impl TA) q c lw) qs"
  have alpha: "map rs.\<alpha> ?results = map rs.\<alpha> ?old"
    using rfc_word_results_impl_eq[
      of "ta_rules_impl TA" "ta_epss_impl TA" c lw qs]
    by simp
  have empty:
    "list_all (\<lambda>res. rs.isEmpty (rs.inter ?qset res)) ?results =
      list_all (\<lambda>res. rs.isEmpty (rs.inter ?qset res)) ?old"
    by (rule list_all_alpha_cong[OF alpha]) (auto simp: rs.correct)
  show ?thesis
    unfolding rfc_rule_no_top_redex_indexed_impl_def
      rfc_rule_no_top_redex_fast_impl_def Let_def
    using Some words empty
    by (simp add: list_all_map_same)
qed

lemma rfc_no_top_redex_indexed_impl_eq:
  "rfc_no_top_redex_indexed_impl TA qs c R =
    rfc_no_top_redex_fast_impl TA qs c R"
  unfolding rfc_no_top_redex_indexed_impl_def
    rfc_no_top_redex_fast_impl_def
  by (induct R) (simp_all add: rfc_rule_no_top_redex_indexed_impl_eq)

definition
  rfc_lifted_lhs_top_impl :: "nat \<Rightarrow> ('f \<times> nat,'v)term \<Rightarrow> bool"
where
  "rfc_lifted_lhs_top_impl c l \<equiv>
    list_all (\<lambda>(f,n). height f = c) (funas_term_list l)"

definition
  rfc_strict_below_bound_list ::
    "(('f \<times> nat,'v)term \<Rightarrow> bool) \<Rightarrow>
    (('f,'v)rule \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow>
    nat \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f \<times> nat,'v)rule list"
where
  "rfc_strict_below_bound_list filt ff c R \<equiv>
    filter (\<lambda>(l,r). \<not> rfc_lifted_lhs_top_impl c l)
      (cover_bound_list_filter filt ff Strict_TRS c R)"

definition
  rfc_initial_paired_accepted_impl ::
    "'f itself \<Rightarrow>
    ('q :: linorder,'f :: linorder \<times> nat) ta_impl \<Rightarrow>
    'q list \<Rightarrow> ('f,string)term list \<Rightarrow> bool"
where
  "rfc_initial_paired_accepted_impl _ TA tails I \<equiv>
    length tails = length I \<and>
    list_all (\<lambda>(t,q).
      rfc_term_accepted_with_tail_states_impl TYPE('f) TA [q] t)
      (zip I tails)"

definition
  check_bounds_generic_rfc_relative ::
    "('f :: {showl,linorder},'q :: {showl,linorder})bounds_info \<Rightarrow>
    ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> showsl check"
where
  "check_bounds_generic_rfc_relative bi R S =
    (case get_integer_bounds_info bi of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
      let c_opt = construct_c_opt c R;
      let RS = R @ S;
      TA \<leftarrow> generate_ta_cond preTA rel;
      let rell = rel_checker rel;
      check_wf_trs RS;
      check (set qfin \<subseteq> rs.\<alpha> (ta_final_impl TA))
        (showsl_lit (STR ''explicitly mentioned final states must be final''));
      check_left_linear_trs RS
        <+? (\<lambda>s. showsl_lit
          (STR ''RFC automaton-closed relative bounds currently require left-linear rules\<newline>'') \<circ> s);
      bounds_condition type RS;
      check_ta_bounded TA c;
      check (Bex (set qfin) (\<lambda>q. rs.memb q (ta_rhs_states_set TA)))
        (showsl_lit (STR ''did not find mentioned final state in TA''));
      state_compatible_eff_list TA rell
        (rfc_strict_below_bound_list (\<lambda>l. \<not> rule_state_compatible_heuristic TA l)
          (boundstype_fun type) c R)
        <+? (\<lambda>(lr,lr_rhs,q). showsl_lit
          (STR ''TA is not compatible with below-top strict RFC TRS\<newline>'')
          \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
          \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
          \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q
          \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''));
      state_compatible_eff_list TA rell
        (cover_bound_list_filter (\<lambda>l. \<not> rule_state_compatible_heuristic TA l)
          Matchbounds.match (Weak_TRS c_opt) c S)
        <+? (\<lambda>(lr,lr_rhs,q). showsl_lit
          (STR ''TA is not compatible with relative RFC TRS\<newline>'')
          \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
          \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lr_rhs
          \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q
          \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''))
    } <+? (\<lambda>s. showsl_lit
      (STR ''problem during checking RFC-relative local bounds conditions of automaton\<newline>'')
      o get_renaming_info ren o showsl_lit (STR ''\<newline>error:\<newline>'') o s))"

lemma rfc_lifted_lhs_top_impl:
  "rfc_lifted_lhs_top_impl c l \<longleftrightarrow>
    (\<forall>f n. (f,n) \<in> funas_term l \<longrightarrow> height f = c)"
  unfolding rfc_lifted_lhs_top_impl_def list_all_iff
  by (auto split: prod.splits)

lemma set_rfc_strict_below_bound_list:
  "set (rfc_strict_below_bound_list filt e c (R :: ('f,'v)rules)) =
    {lr. lr \<in> cover_bound c e Strict_TRS (set R) \<inter>
      {(l,r). (\<forall>u\<unlhd>l. filt u)} \<and> \<not> rfc_lifted_lhs_top_impl c (fst lr)}"
  unfolding rfc_strict_below_bound_list_def
  by (auto simp: cover_bound_list_filter)

lemma check_bounds_generic_rfc_relative_exact:
  assumes ok: "isOK(check_bounds_generic_rfc_relative
    (info :: ('f,'q :: {linorder,showl})bounds_info) (R :: ('f :: {linorder,showl},string)rules) S)"
    and info_def: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel_info, ren)"
  shows "\<exists>rel c_opt.
      rel = relation_of rel_info
      \<and> left_linear_trs (set (R @ S))
      \<and> finite (ta_rules (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
        (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set R) \<inter>
          {(l,r). \<not> rfc_lifted_lhs_top_impl c l})
      \<and> state_compatible (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
        (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))
      \<and> state_coherent (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) rel
      \<and> ta_bounded (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c
      \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> set qfin \<subseteq> ta_final (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)
      \<and> wf_trs (set R \<union> set S)
      \<and> isOK (bounds_condition (boundstype info) (R @ S))
      \<and> weak_kind_condition c c_opt (set R)"
proof -
  from boundstype_get_integer_bounds_info[OF info_def]
  have bt_info[simp]: "boundstype info = type" by auto
  let ?c_opt = "construct_c_opt c R"
  let ?rel = "rel_checker rel_info"
  let ?rell = "relation_of rel_info"
  note ok = ok[unfolded info_def check_bounds_generic_rfc_relative_def, simplified]
  from ok obtain TA where TA: "generate_ta_cond preTA rel_info = return TA" by auto
  from generate_ta_cond[OF this] have inv: "ta_inv TA ?rel ?rell" and TA2: "TA = generate_ta preTA" by auto
  let ?filt = "\<lambda>l. \<not> rule_state_compatible_heuristic TA l"
  let ?e = "boundstype_fun type"
  let ?e2 = Matchbounds.match
  interpret ta_inv TA ?rel ?rell by fact
  have [simp]: "ta_of_ta preTA = TA'" unfolding TA2 generate_ta by simp
  note ok = ok[unfolded TA, simplified]
  from ok have
    wf: "wf_trs (set R \<union> set S)"
    and ll: "left_linear_trs (set (R @ S))"
    and qfin: "\<exists>q\<in>set qfin. rs.memb q (ta_rhs_states_set TA)"
    and c: "isOK(check_ta_bounded TA c)"
    and cond: "isOK(bounds_condition type (R @ S))"
    and compat: "isOK(state_compatible_eff_list TA ?rel
      (rfc_strict_below_bound_list ?filt ?e c R))"
    and compat2: "isOK(state_compatible_eff_list TA ?rel
      (cover_bound_list_filter ?filt ?e2 (Weak_TRS ?c_opt) c S))"
    and final: "set qfin \<subseteq> ta_final (ta_of TA)"
    by (auto simp: ta_final)
  from qfin have qfin: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states TA'"
    using ta_rhs_states_set by (auto simp: rs.correct)
  from c have c': "\<And>fn. fn \<in> set (rm.to_list (ta_rules_impl TA)) \<Longrightarrow>
      case fst fn of (f,n) \<Rightarrow> height f \<le> c"
    unfolding check_ta_bounded_def by auto
  {
    fix f n
    assume "(f,n) \<in> ta_syms TA'"
    then obtain rule where rule: "rule \<in> ta_rules TA'" and n: "r_sym rule = (f,n)"
      unfolding ta_syms_def by auto
    let ?crule = "conv_ta_rule (ta_epss_impl TA) rule"
    from rule have crule: "?crule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'" by auto
    from n have n: "r_sym_impl ?crule = (f,n)" by (cases rule, auto)
    let ?rm = "ta_rules_impl TA"
    from rm_set_lookup3[OF crule, unfolded n]
    obtain rls where "rm.\<alpha> ?rm (f,n) = Some rls" by (force simp: rm_\<alpha>_to_lookup)
    then have "map_of (rm.to_list ?rm) (f,n) = Some rls" by (auto simp: rm.correct)
    from map_of_SomeD[OF this]
    have "((f,n),rls) \<in> set (rm.to_list ?rm)" .
    from c'[OF this] have "height f \<le> c" by simp
  } note c = this
  then have tab: "ta_bounded TA' c" unfolding ta_bounded_def by auto
  note var_cond = wf[unfolded wf_trs_def]
  have compat_below: "state_compatible TA' ?rell
    (cover_bound c ?e Strict_TRS (set R) \<inter> {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
  proof -
    let ?C = "cover_bound c ?e Strict_TRS (set R) \<inter> {(l,r). \<not> rfc_lifted_lhs_top_impl c l}"
    let ?Cf = "?C \<inter> {(l,r). \<forall>u\<unlhd>l. ?filt u}"
    have set_eq: "set (rfc_strict_below_bound_list ?filt ?e c R) = ?Cf"
      by (auto simp: set_rfc_strict_below_bound_list)
    have "state_compatible TA' ?rell (set (rfc_strict_below_bound_list ?filt ?e c R))"
    proof (rule state_compatible_eff_list[OF _ compat])
      fix l r
      assume "(l,r) \<in> set (rfc_strict_below_bound_list ?filt ?e c R)"
      then have "(l,r) \<in> ?Cf" unfolding set_eq .
      then have "(l,r) \<in> cover ?e Strict_TRS (set R)"
        unfolding cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond
      show "vars_term r \<subseteq> vars_term l" by auto
    qed
    then have "state_compatible TA' ?rell ?Cf"
      unfolding set_eq .
    then show ?thesis
    proof (unfold state_compatible_def, intro allI impI)
      fix l r
      assume lr: "(l,r) \<in> ?C"
        and funas: "funas_term l \<subseteq> ta_syms TA'"
      show "rule_state_compatible TA' ?rell (l,r)"
      proof (cases "\<forall>u\<unlhd>l. ?filt u")
        case True
        with lr have "(l,r) \<in> ?Cf" by auto
        with \<open>state_compatible TA' ?rell ?Cf\<close>
        show ?thesis unfolding state_compatible_def using funas by auto
      next
        case False
        then obtain u where subt: "l \<unrhd> u"
          and compat_h: "rule_state_compatible_heuristic TA u"
          by auto
        have "rule_state_compatible TA' (relation_of rel_info) (l,r)"
          by (rule rule_state_compatible_heuristic_subteq[OF compat_h subt])
        then show ?thesis using rel by simp
      qed
    qed
  qed
  have compatS: "state_compatible TA' ?rell (cover_bound c Matchbounds.match (Weak_TRS ?c_opt) (set S))"
  proof -
    let ?C = "cover_bound c Matchbounds.match (Weak_TRS ?c_opt) (set S)"
    let ?Cf = "?C \<inter> {(l,r). \<forall>u\<unlhd>l. ?filt u}"
    have "state_compatible TA' ?rell ?Cf"
    proof (rule state_compatible_eff_list[OF _ compat2, unfolded cover_bound_list_filter])
      fix l r
      assume "(l,r) \<in> ?Cf"
      then have "(l,r) \<in> cover Matchbounds.match (Weak_TRS ?c_opt) (set S)"
        unfolding cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond
      show "vars_term r \<subseteq> vars_term l" by auto
    qed
    then show ?thesis
      by (rule remove_compatible_rules, insert rule_state_compatible_heuristic_subteq, blast)
  qed
  obtain fin rls eps where preTA: "preTA = Tree_Automaton fin rls eps" by (cases preTA, auto)
  from generate_ta_rules[of fin rls eps] have "ta_rules (ta_of TA) = set rls" using TA2 preTA by auto
  then have fin: "finite (ta_rules (ta_of TA))" by auto
  show ?thesis
    by (intro exI[of _ ?rell] exI[of _ ?c_opt] conjI,
      insert ll fin compat_below compatS coherent tab qfin final wf cond TA2, auto)
qed

definition
  check_bounds_generic_native_rfc_relative ::
    "('f :: {showl,linorder},'q :: {showl,linorder})bounds_info \<Rightarrow>
    ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> showsl check"
where
  "check_bounds_generic_native_rfc_relative bi R S =
    (case get_integer_bounds_info bi of
      (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
        let c_opt = construct_c_opt c R;
        let RS = R @ S;
        TA \<leftarrow> generate_ta_cond preTA rel;
        check (rel = Id_Relation)
          (showsl_lit (STR ''native RFC merge currently requires the identity state relation''));
        check (type = Match)
          (showsl_lit (STR ''native RFC relative bounds require non-duplicating match bounds''));
        check_wf_trs RS;
        check (set qfin \<subseteq> rs.\<alpha> (ta_final_impl TA))
          (showsl_lit (STR ''explicitly mentioned final states must be final''));
        check_left_linear_trs RS
          <+? (\<lambda>s. showsl_lit
            (STR ''native RFC relative bounds require left-linear rules\<newline>'') \<circ> s);
        bounds_condition type RS;
        check_ta_bounded TA c;
        check (Bex (set qfin) (\<lambda>q. rs.memb q (ta_rhs_states_set TA)))
          (showsl_lit (STR ''did not find mentioned final state in TA''));
        state_compatible_eff_list TA (rel_checker rel)
          (cover_bound_list_filter
            (\<lambda>l. \<not> rule_state_compatible_heuristic TA l)
            Matchbounds.match (Weak_TRS c_opt) c S)
          <+? (\<lambda>(lr,lr_rhs,q). showsl_lit
            (STR ''TA is not compatible with native RFC residual rules\<newline>'')
            \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr
            \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '')
            \<circ> showsl_rule lr_rhs
            \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q
            \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''))
      } <+? (\<lambda>s. showsl_lit
        (STR ''problem during checking native RFC relative bounds conditions\<newline>'')
        o get_renaming_info ren
        o showsl_lit (STR ''\<newline>error:\<newline>'') o s))"

lemma check_bounds_generic_native_rfc_relative_exact:
  assumes ok: "isOK(check_bounds_generic_native_rfc_relative
    (info :: ('f,'q :: {linorder,showl})bounds_info)
      (R :: ('f :: {linorder,showl},string)rules) S)"
    and info_def: "get_integer_bounds_info info =
      (Bounds_Info type c qfin preTA rel_info, ren)"
  shows "type = Match \<and> rel_info = Id_Relation \<and>
    (\<exists>c_opt.
      left_linear_trs (set (R @ S))
      \<and> finite (ta_rules
        (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> state_compatible
        (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) Id
        (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))
      \<and> ta_bounded
        (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c
      \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states
        (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))
      \<and> set qfin \<subseteq> ta_final
        (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)
      \<and> wf_trs (set R \<union> set S)
      \<and> (\<forall>l r. (l,r) \<in> set (R @ S) \<longrightarrow>
        vars_term_ms r \<subseteq># vars_term_ms l)
      \<and> weak_kind_condition c c_opt (set R))"
proof -
  from boundstype_get_integer_bounds_info[OF info_def]
  have bt_info[simp]: "boundstype info = type" by auto
  let ?c_opt = "construct_c_opt c R"
  note ok = ok[
    unfolded info_def check_bounds_generic_native_rfc_relative_def,
    simplified]
  from ok obtain TA where TA:
    "generate_ta_cond preTA rel_info = return TA"
    by auto
  from generate_ta_cond[OF TA] have inv:
    "ta_inv TA (rel_checker rel_info) (relation_of rel_info)"
    and TA2: "TA = generate_ta preTA"
    by auto
  interpret ta_inv TA "rel_checker rel_info" "relation_of rel_info"
    by (rule inv)
  have [simp]: "ta_of_ta preTA = TA'"
    unfolding TA2 generate_ta by simp
  note ok = ok[unfolded TA, simplified]
  from ok have type: "type = Match"
    and rel: "rel_info = Id_Relation"
    and wf: "wf_trs (set R \<union> set S)"
    and ll: "left_linear_trs (set (R @ S))"
    and qfin: "\<exists>q\<in>set qfin. rs.memb q (ta_rhs_states_set TA)"
    and cb: "isOK(check_ta_bounded TA c)"
    and compat: "isOK(state_compatible_eff_list TA
      (rel_checker rel_info)
      (cover_bound_list_filter
        (\<lambda>l. \<not> rule_state_compatible_heuristic TA l)
        Matchbounds.match (Weak_TRS ?c_opt) c S))"
    and final: "set qfin \<subseteq> ta_final (ta_of TA)"
    by (auto simp: ta_final)
  have cond: "isOK (bounds_condition type (R @ S))"
    using ok by blast
  have nondup: "\<forall>lr\<in>set R \<union> set S.
      case lr of (l,r) \<Rightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
    using cond type by (auto simp: isOK_check_allm split: prod.splits)
  from qfin have qfin':
    "\<exists>q\<in>set qfin. q \<in> ta_rhs_states TA'"
    using ta_rhs_states_set by (auto simp: rs.correct)
  from cb have cb': "\<And>fn.
    fn \<in> set (rm.to_list (ta_rules_impl TA)) \<Longrightarrow>
    case fst fn of (f,n) \<Rightarrow> height f \<le> c"
    unfolding check_ta_bounded_def by auto
  have tab: "ta_bounded TA' c"
  proof (unfold ta_bounded_def, intro allI impI)
    fix f n
    assume "(f,n) \<in> ta_syms TA'"
    then obtain rule where rule: "rule \<in> ta_rules TA'"
      and sym: "r_sym rule = (f,n)"
      unfolding ta_syms_def by auto
    let ?crule = "conv_ta_rule (ta_epss_impl TA) rule"
    from rule have crule:
      "?crule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'"
      by auto
    from sym have rsym: "r_sym_impl ?crule = (f,n)"
      by (cases rule) auto
    from rm_set_lookup3[OF crule, unfolded rsym]
    obtain rls where alpha:
      "rm.\<alpha> (ta_rules_impl TA) (f,n) = Some rls"
      by (force simp: rm_\<alpha>_to_lookup)
    then have map: "map_of (rm.to_list (ta_rules_impl TA)) (f,n) = Some rls"
      by (auto simp: rm.correct)
    from cb'[OF map_of_SomeD[OF map]] show "height f \<le> c"
      by simp
  qed
  note var_cond = wf[unfolded wf_trs_def]
  let ?filt = "\<lambda>l. \<not> rule_state_compatible_heuristic TA l"
  let ?C = "cover_bound c Matchbounds.match
    (Weak_TRS ?c_opt) (set S)"
  let ?Cf = "?C \<inter> {(l,r). \<forall>u\<unlhd>l. ?filt u}"
  have compatS: "state_compatible TA' Id ?C"
  proof -
    have compat_impl: "state_compatible (ta_of TA) (relation_of rel_info)
        (set (cover_bound_list_filter ?filt Matchbounds.match
          (Weak_TRS ?c_opt) c S))"
    proof (rule ta_inv.state_compatible_eff_list[OF inv _ compat])
      fix l r
      assume "(l,r) \<in> set (cover_bound_list_filter ?filt
        Matchbounds.match (Weak_TRS ?c_opt) c S)"
      then have "(l,r) \<in> cover Matchbounds.match
        (Weak_TRS ?c_opt) (set S)"
        unfolding cover_bound_list_filter cover_bound_def by auto
      from cover_var_condition[OF _ this] var_cond
      show "vars_term r \<subseteq> vars_term l" by auto
    qed
    have "state_compatible TA' Id ?Cf"
      using compat_impl rel
      unfolding cover_bound_list_filter by simp
    then show ?thesis
    proof (unfold state_compatible_def, intro allI impI)
      fix l r
      assume lr: "(l,r) \<in> ?C"
        and funas: "funas_term l \<subseteq> ta_syms TA'"
      show "rule_state_compatible TA' Id (l,r)"
      proof (cases "\<forall>u\<unlhd>l. ?filt u")
        case True
        with lr have "(l,r) \<in> ?Cf" by auto
        with \<open>state_compatible TA' Id ?Cf\<close>
        show ?thesis
          unfolding state_compatible_def using funas by auto
      next
        case False
        then obtain u where subt: "l \<unrhd> u"
          and compat_h: "rule_state_compatible_heuristic TA u"
          by auto
        have "rule_state_compatible TA' (relation_of rel_info) (l,r)"
          by (rule rule_state_compatible_heuristic_subteq[OF compat_h subt])
        then show ?thesis using rel by simp
      qed
    qed
  qed
  obtain fin rls eps where preTA:
    "preTA = Tree_Automaton fin rls eps"
    by (cases preTA) auto
  from generate_ta_rules[of fin rls eps]
  have rules: "ta_rules (ta_of TA) = set rls"
    using TA2 preTA by auto
  have finite: "finite (ta_rules (ta_of TA))"
    unfolding rules by auto
  show ?thesis
    using type rel ll finite compatS tab qfin' final wf nondup TA2
    by (intro conjI exI[of _ ?c_opt]) auto
qed

definition
  rfc_rule_matchbox_closed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_matchbox_closed_impl TA rel qs lr \<equiv> (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        list_all (\<lambda>q.
          rel_checker rel
            (rfc_word_res_impl
              (ta_rules_impl TA) (ta_epss_impl TA) q 0 lw)
            (rfc_word_res_impl
              (ta_rules_impl TA) (ta_epss_impl TA) q 0 rw) = None)
          qs)"

definition
  rfc_matchbox_closed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_matchbox_closed_impl TA rel qs R \<equiv>
    list_all (rfc_rule_matchbox_closed_impl TA rel qs) R"

definition
  rfc_rule_native_matchbox_closed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_native_matchbox_closed_impl TA rel qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        list_all (\<lambda>q.
          rel_checker rel
            (rfc_native_word_res_impl
              (ta_rules_impl TA) (ta_epss_impl TA) q 0 lw)
            (rfc_native_word_res_impl
              (ta_rules_impl TA) (ta_epss_impl TA) q 0 rw) = None)
          qs)"

definition
  rfc_native_matchbox_closed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_native_matchbox_closed_impl TA rel qs R \<equiv>
    list_all (rfc_rule_native_matchbox_closed_impl TA rel qs) R"

definition
  rfc_rule_native_matchbox_ext_right_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_native_matchbox_ext_right_impl TA rel tails lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        lw \<noteq> [] \<and>
        list_all (\<lambda>q.
          let rhs = rfc_native_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q 0 rw
          in list_all (\<lambda>i.
            rel_checker rel
              (rfc_native_word_res_impl
                (ta_rules_impl TA) (ta_epss_impl TA) q 0 (take i lw))
              rhs = None)
            [1..<length lw])
          tails)"

definition
  rfc_native_matchbox_ext_right_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_native_matchbox_ext_right_impl TA rel tails R \<equiv>
    list_all (rfc_rule_native_matchbox_ext_right_impl TA rel tails) R"

definition
  rfc_rule_native_no_top_redex_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_native_no_top_redex_impl TA qs c lr \<equiv>
    (let qset = rs.from_list qs in
      case rfc_rule_words lr of
        None \<Rightarrow> False
      | Some (lw, rw) \<Rightarrow>
          list_all (\<lambda>q.
            rs.isEmpty (rs.inter qset
              (rfc_native_word_res_impl
                (ta_rules_impl TA) (ta_epss_impl TA) q c lw)))
            qs)"

definition
  rfc_native_no_top_redex_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_native_no_top_redex_impl TA qs c R \<equiv>
    list_all (rfc_rule_native_no_top_redex_impl TA qs c) R"

definition
  rfc_rule_native_inner_splice_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_native_inner_splice_impl TA qs c lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        lw \<noteq> [] \<and>
        list_all (\<lambda>q.
          list_all (\<lambda>lfhs.
            let lhs = rfc_native_labeled_word_res_impl
              (ta_rules_impl TA) (ta_epss_impl TA) q lfhs;
                h = min c (Suc (rfc_labeled_min_height lfhs));
                rfhs = map (\<lambda>f. (f,h)) rw
            in list_all (\<lambda>p.
              if rw = [] then
                rs.memb p (ta_epss_impl TA q)
              else
                list_ex (\<lambda>s.
                  let rhs = rfc_native_labeled_word_res_impl
                    (ta_rules_impl TA) (ta_epss_impl TA) s rfhs
                  in list_ex (\<lambda>e. rs.memb p (ta_epss_impl TA e))
                    (rs.to_list rhs))
                  (rs.to_list (ta_epss_impl TA q)))
              (rs.to_list lhs))
            (rfc_labeled_height_vectors c lw))
          qs)"

definition
  rfc_native_inner_splice_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q list \<Rightarrow> nat \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_native_inner_splice_impl TA qs c R \<equiv>
    list_all (rfc_rule_native_inner_splice_impl TA qs c) R"

definition
  rfc_rule_matchbox_closed_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_matchbox_closed_indexed_impl TA rel qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
          (rfc_word_results_impl
            (ta_rules_impl TA) (ta_epss_impl TA) 0 lw qs)
          (rfc_word_results_impl
            (ta_rules_impl TA) (ta_epss_impl TA) 0 rw qs))"

definition
  rfc_matchbox_closed_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> ('f,string)rules \<Rightarrow> bool"
where
  "rfc_matchbox_closed_indexed_impl TA rel qs R \<equiv>
    list_all (rfc_rule_matchbox_closed_indexed_impl TA rel qs) R"

lemma rfc_rule_matchbox_closed_indexed_impl_eq:
  "rfc_rule_matchbox_closed_indexed_impl TA rel qs lr =
    rfc_rule_matchbox_closed_impl TA rel qs lr"
proof (cases "rfc_rule_words lr")
  case None
  then show ?thesis
    by (simp add: rfc_rule_matchbox_closed_indexed_impl_def
      rfc_rule_matchbox_closed_impl_def)
next
  case (Some words)
  then obtain lw rw where words: "words = (lw,rw)"
    by (cases words)
  show ?thesis
    unfolding rfc_rule_matchbox_closed_indexed_impl_def
      rfc_rule_matchbox_closed_impl_def
    using Some words
      rfc_word_results_rel_checker[
        of rel "ta_rules_impl TA" "ta_epss_impl TA" 0 lw qs rw]
    by simp
qed

lemma rfc_matchbox_closed_indexed_impl_eq:
  "rfc_matchbox_closed_indexed_impl TA rel qs R =
    rfc_matchbox_closed_impl TA rel qs R"
  unfolding rfc_matchbox_closed_indexed_impl_def
    rfc_matchbox_closed_impl_def
  by (induct R) (simp_all add: rfc_rule_matchbox_closed_indexed_impl_eq)

definition
  rfc_rule_matchbox_ext_right_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> 'q list \<Rightarrow>
      ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_matchbox_ext_right_impl TA rel tails qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        lw \<noteq> [] \<and>
        list_all (\<lambda>q.
          let rhs = rfc_word_res_impl
            (ta_rules_impl TA) (ta_epss_impl TA) q 0 rw in
          list_all (\<lambda>i.
            let prefix = take i lw in
            rel_checker rel
              (rfc_word_res_impl
                (ta_rules_impl TA) (ta_epss_impl TA) q 0 prefix)
              rhs = None)
            [1..<length lw])
          tails)"

definition
  rfc_matchbox_ext_right_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> 'q list \<Rightarrow>
      ('f,string)rules \<Rightarrow> bool"
where
  "rfc_matchbox_ext_right_impl TA rel tails qs R \<equiv>
    list_all (rfc_rule_matchbox_ext_right_impl TA rel tails qs) R"

definition
  rfc_rule_matchbox_ext_right_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> 'q list \<Rightarrow>
      ('f,string)rule \<Rightarrow> bool"
where
  "rfc_rule_matchbox_ext_right_indexed_impl TA rel tails qs lr \<equiv>
    (case rfc_rule_words lr of
      None \<Rightarrow> False
    | Some (lw, rw) \<Rightarrow>
        lw \<noteq> [] \<and>
        (let rhs = rfc_word_results_impl
            (ta_rules_impl TA) (ta_epss_impl TA) 0 rw tails in
          list_all (\<lambda>i.
            let prefix = take i lw in
            list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
              (rfc_word_results_impl
                (ta_rules_impl TA) (ta_epss_impl TA) 0 prefix tails)
              rhs)
            [1..<length lw]))"

definition
  rfc_matchbox_ext_right_indexed_impl ::
    "('q :: linorder, 'f :: linorder \<times> nat) ta_impl \<Rightarrow>
      'q ta_relation \<Rightarrow> 'q list \<Rightarrow> 'q list \<Rightarrow>
      ('f,string)rules \<Rightarrow> bool"
where
  "rfc_matchbox_ext_right_indexed_impl TA rel tails qs R \<equiv>
    list_all
      (rfc_rule_matchbox_ext_right_indexed_impl TA rel tails qs) R"

lemma list_all_swap:
  "list_all (\<lambda>x. list_all (\<lambda>y. P x y) ys) xs =
    list_all (\<lambda>y. list_all (\<lambda>x. P x y) xs) ys"
  unfolding list_all_iff
  by auto

lemma rfc_rule_matchbox_ext_right_indexed_impl_eq:
  "rfc_rule_matchbox_ext_right_indexed_impl TA rel tails qs lr =
    rfc_rule_matchbox_ext_right_impl TA rel tails qs lr"
proof (cases "rfc_rule_words lr")
  case None
  then show ?thesis
    by (simp add: rfc_rule_matchbox_ext_right_indexed_impl_def
      rfc_rule_matchbox_ext_right_impl_def)
next
  case (Some words)
  then obtain lw rw where words: "words = (lw,rw)"
    by (cases words)
  have each: "\<And>i.
    list_all2 (\<lambda>lhs rhs. rel_checker rel lhs rhs = None)
      (rfc_word_results_impl
        (ta_rules_impl TA) (ta_epss_impl TA) 0 (take i lw) tails)
      (rfc_word_results_impl
        (ta_rules_impl TA) (ta_epss_impl TA) 0 rw tails) =
    list_all (\<lambda>q.
      rel_checker rel
        (rfc_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q 0 (take i lw))
        (rfc_word_res_impl
          (ta_rules_impl TA) (ta_epss_impl TA) q 0 rw) = None)
      tails"
    by (rule rfc_word_results_rel_checker)
  show ?thesis
    unfolding rfc_rule_matchbox_ext_right_indexed_impl_def
      rfc_rule_matchbox_ext_right_impl_def Let_def
    using Some words
    by (simp only: option.case(2) prod.case each)
      (rule arg_cong[where f = "\<lambda>x. lw \<noteq> [] \<and> x"],
        rule list_all_swap)
qed

lemma rfc_matchbox_ext_right_indexed_impl_eq:
  "rfc_matchbox_ext_right_indexed_impl TA rel tails qs R =
    rfc_matchbox_ext_right_impl TA rel tails qs R"
  unfolding rfc_matchbox_ext_right_indexed_impl_def
    rfc_matchbox_ext_right_impl_def
  by (induct R)
    (simp_all add: rfc_rule_matchbox_ext_right_indexed_impl_eq)

definition productive_tree_automaton ::
  "('q :: compare_order, 'f :: compare_order) tree_automaton \<Rightarrow> ('q,'f) tree_automaton"
where
  "productive_tree_automaton TA \<equiv>
    Tree_Automaton
      (sorted_list_of_set (ta_final (ta_only_prod (ta_of_ta TA))))
      (sorted_list_of_set (ta_rules (ta_only_prod (ta_of_ta TA))))
      (sorted_list_of_set (ta_eps (ta_only_prod (ta_of_ta TA))))"

definition productive_bounds_info ::
  "('f :: compare_order, 'q :: compare_order) bounds_info \<Rightarrow> ('f,'q) bounds_info"
where
  "productive_bounds_info info \<equiv>
    case info of Bounds_Info type c qfin preTA rel \<Rightarrow>
      Bounds_Info type c qfin (productive_tree_automaton preTA) rel"

lemma boundstype_productive_bounds_info[simp]:
  "boundstype (productive_bounds_info info) = boundstype info"
  by (cases info) (simp add: productive_bounds_info_def)

definition
  rfc_automaton_closed_relative_bounds_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{compare_order,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    ('f,string)rules \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "rfc_automaton_closed_relative_bounds_tt I info initial_terms Rdelete tp \<equiv>
    (case get_integer_bounds_info info of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
      TA \<leftarrow> generate_ta_cond preTA rel;
      let states = remdups (states_of_tree_automata_dup preTA);
      let Rstrict = tp_ops.R I tp;
      let Rkeep = ceta_list_diff Rstrict Rdelete;
      check (tp_ops.Q_empty I tp)
        (showsl_lit (STR ''RFC automaton-closed relative bounds currently require an empty Q component''));
      check (tp_ops.Rw I tp = [])
        (showsl_lit (STR ''RFC automaton-closed relative bounds currently require no weak rules''));
      check (\<not> tp_ops.nfs I tp)
        (showsl_lit (STR ''RFC automaton-closed relative bounds currently certify full rewriting, not innermost rewriting''));
      check_subseteq Rdelete Rstrict
        <+? (\<lambda> lr. showsl_lit (STR ''could not find removed rule '') \<circ> showsl_rule lr
          \<circ> showsl_lit (STR '' among current strict rules''));
      check (boundstype info = Match)
        (showsl_lit (STR ''RFC automaton-closed relative bounds require boundstype match''));
      check_wf_trs Rstrict;
      check (list_all (\<lambda>(l,r). linear_term r) Rstrict)
        (showsl_lit (STR ''RFC automaton-closed relative bounds require right-linear rules''));
      check (rfc_initial_single_var initial_terms)
        (showsl_lit (STR ''RFC automaton-closed relative initial language templates must contain at most one variable''));
      check (rfc_initial_covers Rstrict initial_terms)
        (showsl_lit (STR ''RFC automaton-closed relative initial language does not contain all right-hand sides''));
      check (rfc_initial_accepted_with_tail_states_impl TYPE('f) TA states initial_terms)
        (showsl_lit (STR ''RFC automaton-closed relative initial language is not accepted by the automaton for all automaton states''));
      check (rfc_automaton_closed_impl TA states Rstrict)
        (showsl_lit (STR ''RFC automaton-closed relative split condition failed''));
      check (rfc_lhs_suffix_total_impl TA states Rstrict)
        (showsl_lit (STR ''RFC automaton-closed relative lhs suffix totality condition failed''));
      check (rfc_no_top_redex_impl TA states c Rdelete)
        (showsl_lit (STR ''RFC automaton-closed relative removed rules have a redex at the top match-bound layer''));
      check_bounds_generic_rfc_relative info Rdelete Rkeep;
      return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) Rkeep Rdelete)
    })"

definition
  rfc_matchbox_relative_bounds_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{compare_order,showl}, 'q::{compare_order,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    ('f,string)rules \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "rfc_matchbox_relative_bounds_tt I info initial_terms Rdelete tp \<equiv>
    (case get_integer_bounds_info info of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
      TA \<leftarrow> generate_ta_cond preTA rel;
      let states = remdups (states_of_tree_automata_dup preTA);
      let Rstrict = tp_ops.R I tp;
      let Rkeep = ceta_list_diff Rstrict Rdelete;
      check (tp_ops.Q_empty I tp)
        (showsl_lit (STR ''RFC Matchbox-relative bounds currently require an empty Q component''));
      check (tp_ops.Rw I tp = [])
        (showsl_lit (STR ''RFC Matchbox-relative bounds currently require no weak rules''));
      check (\<not> tp_ops.nfs I tp)
        (showsl_lit (STR ''RFC Matchbox-relative bounds currently certify full rewriting, not innermost rewriting''));
      check_subseteq Rdelete Rstrict
        <+? (\<lambda> lr. showsl_lit (STR ''could not find removed rule '') \<circ> showsl_rule lr
          \<circ> showsl_lit (STR '' among current strict rules''));
      check (boundstype info = Match)
        (showsl_lit (STR ''RFC Matchbox-relative bounds require boundstype match''));
      check_wf_trs Rstrict;
      check (list_all (\<lambda>(l,r). linear_term r) Rstrict)
        (showsl_lit (STR ''RFC Matchbox-relative bounds require right-linear rules''));
      check (rfc_initial_single_var initial_terms)
        (showsl_lit (STR ''RFC Matchbox-relative initial language templates must contain at most one variable''));
      check (rfc_initial_covers Rstrict initial_terms)
        (showsl_lit (STR ''RFC Matchbox-relative initial language does not cover all right-hand sides''));
      check (list_all (\<lambda>q. rs.memb q (ta_rhs_states_set TA)) qfin)
        (showsl_lit (STR ''RFC Matchbox-relative tail states must occur as automaton right-hand-side states''));
      check (rfc_initial_paired_accepted_impl TYPE('f) TA qfin initial_terms)
        (showsl_lit (STR ''RFC Matchbox-relative right-hand sides are not accepted by their paired tail states''));
      check (rfc_matchbox_closed_indexed_impl TA rel states Rstrict)
        (showsl_lit (STR ''RFC Matchbox-relative merge/epsilon split condition failed''));
      check (rfc_matchbox_ext_right_indexed_impl TA rel qfin states Rstrict)
        (showsl_lit (STR ''RFC Matchbox-relative right-extension condition failed''));
      check (rfc_no_top_redex_indexed_impl TA states c Rdelete)
        (showsl_lit (STR ''RFC Matchbox-relative removed rules have a redex at the top match-bound layer''));
      check_bounds_generic_rfc_relative info Rdelete Rkeep;
      return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) Rkeep Rdelete)
    })"

definition
  rfc_native_matchbox_relative_bounds_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{compare_order,showl}, 'q::{compare_order,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    ('f,string)rules \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "rfc_native_matchbox_relative_bounds_tt I info initial_terms Rdelete tp \<equiv>
    (case get_integer_bounds_info info of
      (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
        TA \<leftarrow> generate_ta_cond preTA rel;
        let states = remdups (states_of_tree_automata_dup preTA);
        let Rstrict = tp_ops.R I tp;
        let Rkeep = ceta_list_diff Rstrict Rdelete;
        check (tp_ops.Q_empty I tp)
          (showsl_lit (STR ''native RFC bounds require an empty Q component''));
        check (tp_ops.Rw I tp = [])
          (showsl_lit (STR ''native RFC bounds require no weak rules''));
        check (\<not> tp_ops.nfs I tp)
          (showsl_lit (STR ''native RFC bounds certify full rewriting''));
        check_subseteq Rdelete Rstrict
          <+? (\<lambda>lr. showsl_lit (STR ''could not find removed rule '')
            \<circ> showsl_rule lr);
        check (boundstype info = Match)
          (showsl_lit (STR ''native RFC bounds require boundstype match''));
        check_wf_trs Rstrict;
        check (list_all (\<lambda>(l,r). linear_term r) Rstrict)
          (showsl_lit (STR ''native RFC bounds require right-linear rules''));
        check (rfc_initial_single_var initial_terms)
          (showsl_lit (STR ''native RFC initial templates contain too many variables''));
        check (rfc_initial_covers Rstrict initial_terms)
          (showsl_lit (STR ''native RFC initial language misses a right-hand side''));
        check (list_all (\<lambda>q. rs.memb q (ta_rhs_states_set TA)) qfin)
          (showsl_lit (STR ''native RFC tail state is not a right-hand-side state''));
        check (rfc_initial_paired_accepted_impl TYPE('f) TA qfin initial_terms)
          (showsl_lit (STR ''native RFC initial language is not accepted''));
        check (rfc_native_matchbox_closed_impl TA Id_Relation states Rstrict)
          (showsl_lit (STR ''native RFC merge closure failed''));
        check (rfc_native_matchbox_ext_right_impl TA Id_Relation states Rstrict)
          (showsl_lit (STR ''native RFC right-extension closure failed''));
        check (rfc_native_inner_splice_impl TA states c Rdelete)
          (showsl_lit (STR ''native RFC bounded inner-splice closure failed''));
        check (rfc_native_no_top_redex_impl TA states c Rdelete)
          (showsl_lit (STR ''native RFC removed rule has a top-layer redex''));
        check_bounds_generic_native_rfc_relative info Rdelete Rkeep;
        return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) Rkeep Rdelete)
      })"

lemma lift_term_map_funs_term:
  "lift_term h t = map_funs_term (\<lambda>a. (a, h)) t"
  by (induct t) auto

lemma lift_base_term_if_rfc_lifted_lhs_top_impl:
  assumes "rfc_lifted_lhs_top_impl c l"
  shows "lift_term c (base_term l) = l"
  using assms
proof (induct l)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have f: "(base f, c) = f"
    using Fun.prems
    unfolding rfc_lifted_lhs_top_impl_def list_all_iff
    by (cases f) auto
  have ts: "map (lift_term c \<circ> base_term) ts = ts"
  proof (rule map_idI)
    fix t
    assume t: "t \<in> set ts"
    have "rfc_lifted_lhs_top_impl c t"
      using Fun.prems t
      unfolding rfc_lifted_lhs_top_impl_def list_all_iff
      by auto
    then show "(lift_term c \<circ> base_term) t = t"
      using Fun.hyps[OF t] by (simp add: lift_term_map_funs_term)
  qed
  have ts': "map (map_funs_term (\<lambda>a. (a, c)) \<circ> base_term) ts = ts"
  proof (rule map_idI)
    fix t
    assume t: "t \<in> set ts"
    have top_t: "rfc_lifted_lhs_top_impl c t"
      using Fun.prems t
      unfolding rfc_lifted_lhs_top_impl_def list_all_iff
      by auto
    have "map_funs_term (\<lambda>a. (a, c)) (base_term t) = t"
      using Fun.hyps[OF t top_t]
      unfolding lift_term_map_funs_term .
    then show "(map_funs_term (\<lambda>a. (a, c)) \<circ> base_term) t = t"
      by simp
  qed
  show ?case
    by (simp add: f ts' lift_term_map_funs_term)
qed

lemma funas_lift_term_ta_lang_subset:
  fixes TA :: "('q,'f \<times> nat)ta"
    and u :: "('f,string)term"
  assumes lang: "lift_term 0 u \<in> (ta_lang TA :: ('f \<times> nat,string)terms)"
  shows "funas_term u \<subseteq> unlift_sig ` ta_syms TA"
proof
  fix sym
  assume sym_u: "sym \<in> funas_term u"
  have lift_sym: "lift_sig 0 sym \<in> funas_term (lift_term 0 u)"
    by (rule funas_term_lift_sigI) (fact sym_u)
  have lift_in: "lift_sig 0 sym \<in> ta_syms TA"
    by (rule subsetD[OF ta_syms_lang[OF lang] lift_sym])
  have "unlift_sig (lift_sig 0 sym) \<in> unlift_sig ` ta_syms TA"
    by (rule imageI[OF lift_in])
  then show "sym \<in> unlift_sig ` ta_syms TA"
    by simp
qed

lemma ta_states_generate_ta_states_of_tree_automata_dup:
  "ta_states (ta_of (generate_ta preTA)) \<subseteq> set (states_of_tree_automata_dup preTA)"
  by (cases preTA)
    (auto simp: generate_ta_rules generate_ta_eps generate_ta_final ta_states_def r_states_def)

lemma rfc_word_ta_res_append:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes m: "m \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))"
    and p: "p \<in> ta_res TA (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
  shows "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
  using p
proof (induct xs arbitrary: p)
  case Nil
  then show ?case
    using m by (auto intro: ta_res_eps simp: lift_term_map_funs_term)
next
  case (Cons f xs)
  from Cons.prems obtain p' qs where rule: "((f,0) qs \<rightarrow> p') \<in> ta_rules TA"
    and eps: "(p', p) \<in> (ta_eps TA)\<^sup>*"
    and len: "length qs = Suc 0"
    and arg: "qs ! 0 \<in> ta_res TA
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
    by (auto simp: lift_term_map_funs_term)
  have arg': "qs ! 0 \<in> ta_res TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
    by (rule Cons.hyps[OF arg])
  show ?case
    using rule eps len arg' by (auto simp: lift_term_map_funs_term)
qed

lemma rfc_word_ta_res_append_ex:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes p: "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
  shows "\<exists>m.
    m \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))
    \<and> p \<in> ta_res TA (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
  using p
proof (induct xs arbitrary: p)
  case Nil
  have "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))"
    using Nil.prems by (simp add: lift_term_map_funs_term)
  moreover have "p \<in> ta_res TA (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term [] ''x'')))"
    by (auto simp: lift_term_map_funs_term)
  ultimately show ?case
    by blast
next
  case (Cons f xs)
  from Cons.prems obtain p' qs where rule: "((f,0) qs \<rightarrow> p') \<in> ta_rules TA"
    and eps: "(p', p) \<in> (ta_eps TA)\<^sup>*"
    and len: "length qs = Suc 0"
    and arg: "qs ! 0 \<in> ta_res TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
    by (auto simp: lift_term_map_funs_term)
  from Cons.hyps[OF arg] obtain m where
    suffix: "m \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))"
    and prefix: "qs ! 0 \<in> ta_res TA (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
    by blast
  have "p \<in> ta_res TA (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (f # xs) ''x'')))"
    using rule eps len prefix by (auto simp: lift_term_map_funs_term)
  with suffix show ?case
    by blast
qed

lemma rfc_word_ta_res_appendE:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes p: "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
  obtains m where
    "m \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))"
    "p \<in> ta_res TA (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
  using rfc_word_ta_res_append_ex[OF p] by blast

lemma rfc_word_reaches_impl_append:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel_info rel"
    and suffix: "rfc_word_reaches_impl TAi q ys m"
    and prefix: "rfc_word_reaches_impl TAi m xs p"
  shows "rfc_word_reaches_impl TAi q (xs @ ys) p"
proof -
  from rfc_word_reaches_impl_sound[OF inv suffix]
  have suffix': "m \<in> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))" .
  from rfc_word_reaches_impl_sound[OF inv prefix]
  have prefix': "p \<in> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))" .
  from rfc_word_ta_res_append[OF suffix' prefix']
  show ?thesis
    by (rule rfc_word_reaches_impl_complete[OF inv])
qed

lemma rfc_rule_no_top_redex_fast_impl_imp:
  assumes fast: "rfc_rule_no_top_redex_fast_impl TA qs c lr"
  shows "\<not> rfc_rule_has_top_redex_impl TA qs c lr"
proof (cases "rfc_rule_words lr")
  case None
  then show ?thesis
    using fast unfolding rfc_rule_no_top_redex_fast_impl_def
      rfc_rule_has_top_redex_impl_def by simp
next
  case (Some words)
  obtain lw rw where words: "words = (lw,rw)"
    by (cases words) auto
  have rule_words: "rfc_rule_words lr = Some (lw,rw)"
    using Some words by simp
  from fast show ?thesis
    unfolding rfc_rule_no_top_redex_fast_impl_def
      rfc_rule_has_top_redex_impl_def rfc_word_reaches_height_impl_def rule_words
    by (auto simp: list_all_iff rs.correct)
qed

lemma rfc_no_top_redex_fast_impl_imp:
  assumes fast: "rfc_no_top_redex_fast_impl TA qs c R"
  shows "rfc_no_top_redex_impl TA qs c R"
proof -
  have fast_rule: "\<And>lr. lr \<in> set R \<Longrightarrow>
      rfc_rule_no_top_redex_fast_impl TA qs c lr"
    using fast unfolding rfc_no_top_redex_fast_impl_def
    by (auto simp: list_all_iff)
  have slow_rule: "\<And>lr. lr \<in> set R \<Longrightarrow>
      \<not> rfc_rule_has_top_redex_impl TA qs c lr"
    by (intro rfc_rule_no_top_redex_fast_impl_imp fast_rule)
  show ?thesis
    unfolding rfc_no_top_redex_impl_def
    using slow_rule by (auto simp: list_all_iff)
qed

lemma rfc_word_ta_res_state:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes q: "q \<in> ta_states TA"
    and p: "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term w ''x'')))"
  shows "p \<in> ta_states TA"
  using p
proof (induct w arbitrary: p)
  case Nil
  then show ?case
    using q by (auto intro: ta_eps_ta_states simp: lift_term_map_funs_term)
next
  case (Cons f w)
  from Cons.prems obtain p' qs where rule: "((f,0) qs \<rightarrow> p') \<in> ta_rules TA"
    and eps: "(p', p) \<in> (ta_eps TA)\<^sup>*"
    by (auto simp: lift_term_map_funs_term)
  have "p' \<in> ta_states TA"
    by (rule r_rhs_states[OF rule])
  then show ?case
    using eps by (rule ta_eps_ta_states)
qed

lemma rfc_word_ta_res_state_height:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes q: "q \<in> ta_states TA"
    and p: "p \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w ''x'')))"
  shows "p \<in> ta_states TA"
  using p
proof (induct w arbitrary: p)
  case Nil
  then show ?case
    using q by (auto intro: ta_eps_ta_states simp: lift_term_map_funs_term)
next
  case (Cons f w)
  from Cons.prems obtain p' qs where rule: "((f,h) qs \<rightarrow> p') \<in> ta_rules TA"
    and eps: "(p', p) \<in> (ta_eps TA)\<^sup>*"
    by (auto simp: lift_term_map_funs_term)
  have "p' \<in> ta_states TA"
    by (rule r_rhs_states[OF rule])
  then show ?case
    using eps by (rule ta_eps_ta_states)
qed

lemma map_vars_lift_rfc_word_term_tail_irrel_height:
  "map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w x)) =
    map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w y))"
  by (induct w) auto

lemma map_vars_lift_rfc_word_term_tail_subst:
  "map_vars_term \<sigma> (lift_term h (rfc_word_term w x)) =
    map_vars_term (\<lambda>_. \<sigma> x) (lift_term h (rfc_word_term w y))"
  by (induct w) auto

fun rfc_word_ctxt :: "'f list \<Rightarrow> ('f \<times> nat,'q)ctxt"
where
  "rfc_word_ctxt [] = Hole"
| "rfc_word_ctxt (f # fs) = More (f,0) [] (rfc_word_ctxt fs) []"

lemma rfc_word_ctxt_apply:
  "(rfc_word_ctxt w)\<langle>Var q\<rangle> =
    map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term w x))"
  by (induct w) auto

lemma rfc_word_reaches_height_impl_sound:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and reach: "rfc_word_reaches_height_impl TA q h w p"
  shows "p \<in> ta_res (ta_of TA)
    (map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w ''x'')))"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
    using reach unfolding rfc_word_reaches_height_impl_def by (simp add: ta_res_impl rs.correct)
qed

lemma rfc_word_reaches_height_impl_complete:
  fixes TA :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TA rel rell"
    and reach: "p \<in> ta_res (ta_of TA)
      (map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w ''x'')))"
  shows "rfc_word_reaches_height_impl TA q h w p"
proof -
  interpret ta_inv TA rel rell by (rule inv)
  show ?thesis
    using reach unfolding rfc_word_reaches_height_impl_def by (simp add: ta_res_impl rs.correct)
qed

lemma rfc_rule_has_top_redex_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and redex: "rfc_rule_has_top_redex_impl TAi qs c lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
  shows "\<exists>q\<in>set qs. \<exists>p\<in>set qs.
    p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term c (rfc_word_term lw ''x'')))"
proof -
  from redex words obtain q p where q: "q \<in> set qs" and p: "p \<in> set qs"
    and reach: "rfc_word_reaches_height_impl TAi q c lw p"
    unfolding rfc_rule_has_top_redex_impl_def list_all_iff by auto
  from rfc_word_reaches_height_impl_sound[OF inv reach]
  show ?thesis using q p by blast
qed

lemma rfc_no_top_redex_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and no_top: "rfc_no_top_redex_impl TAi qs c R"
    and lr: "lr \<in> set R"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and q: "q \<in> set qs"
    and p: "p \<in> set qs"
  shows "p \<notin> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term c (rfc_word_term lw ''x'')))"
proof
  assume reach: "p \<in> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term c (rfc_word_term lw ''x'')))"
  have reach_impl: "rfc_word_reaches_height_impl TAi q c lw p"
    by (rule rfc_word_reaches_height_impl_complete[OF inv reach])
  have "rfc_rule_has_top_redex_impl TAi qs c lr"
    unfolding rfc_rule_has_top_redex_impl_def words
    using q p reach_impl by (auto simp: list_all_iff)
  with no_top lr show False
    unfolding rfc_no_top_redex_impl_def list_all_iff by auto
qed

lemma rfc_no_top_redex_impl_rule_words:
  assumes no_top: "rfc_no_top_redex_impl TA qs c R"
    and lr: "lr \<in> set R"
  shows "\<exists>lw rw. rfc_rule_words lr = Some (lw, rw)"
  using no_top lr
  unfolding rfc_no_top_redex_impl_def rfc_rule_has_top_redex_impl_def list_all_iff
  by (cases "rfc_rule_words lr") auto

lemma rfc_no_top_redex_full_strict_compat:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and below: "state_compatible (ta_of TAi) rell
      (cover_bound c Matchbounds.match Strict_TRS (set R) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
    and no_top: "rfc_no_top_redex_impl TAi qs c R"
  shows "state_compatible (ta_of TAi) rell
    (cover_bound c Matchbounds.match Strict_TRS (set R))"
proof (unfold state_compatible_def, intro allI impI)
  fix l r
  let ?TA = "ta_of TAi"
  assume lr: "(l, r) \<in> cover_bound c Matchbounds.match Strict_TRS (set R)"
    and funas: "funas_term l \<subseteq> ta_syms ?TA"
  show "rule_state_compatible ?TA rell (l, r)"
  proof (cases "rfc_lifted_lhs_top_impl c l")
    case False
    with below lr funas show ?thesis
      unfolding state_compatible_def by auto
  next
    case True
    from lr obtain bl br h where base_lr: "(bl, br) \<in> set R"
      and base_l: "base_term l = bl"
      and r: "r = lift_term h br"
      unfolding cover_bound_def cover_def by auto
    from rfc_no_top_redex_impl_rule_words[OF no_top base_lr]
    obtain lw rw where words: "rfc_rule_words (bl, br) = Some (lw, rw)"
      by auto
    from rfc_rule_words_sound[OF words]
    obtain x where bl: "bl = rfc_word_term lw x"
      and br: "br = rfc_word_term rw x"
      by auto
    have l_word: "l = lift_term c (rfc_word_term lw x)"
      using lift_base_term_if_rfc_lifted_lhs_top_impl[OF True] base_l bl
      by simp
    have inner: "\<forall>\<sigma>. \<sigma> ` vars_term l \<subseteq> ta_rhs_states ?TA \<longrightarrow>
      ta_res ?TA (map_vars_term \<sigma> l) \<subseteq>
        rell\<inverse> `` ta_res ?TA (map_vars_term \<sigma> r)"
    proof (intro allI impI subsetI)
      fix \<sigma> p
      assume sig: "\<sigma> ` vars_term l \<subseteq> ta_rhs_states ?TA"
        and p: "p \<in> ta_res ?TA (map_vars_term \<sigma> l)"
      have x_rhs: "\<sigma> x \<in> ta_rhs_states ?TA"
        using sig unfolding l_word by auto
      then have x_state: "\<sigma> x \<in> ta_states ?TA"
        using ta_rhs_states_subset_states[of ?TA] by blast
      then have x_qs: "\<sigma> x \<in> set qs"
        using state_cover by auto
      have lhs_irrel: "map_vars_term \<sigma> l =
        map_vars_term (\<lambda>_. \<sigma> x) (lift_term c (rfc_word_term lw ''x''))"
        unfolding l_word
        by (rule map_vars_lift_rfc_word_term_tail_subst)
      have p_state: "p \<in> ta_states ?TA"
        using x_state p unfolding lhs_irrel
        by (rule rfc_word_ta_res_state_height)
      then have p_qs: "p \<in> set qs"
        using state_cover by auto
      from rfc_no_top_redex_implD[OF inv no_top base_lr words x_qs p_qs]
      have "p \<notin> ta_res ?TA
        (map_vars_term (\<lambda>_. \<sigma> x) (lift_term c (rfc_word_term lw ''x'')))" .
      with p lhs_irrel show "p \<in> rell\<inverse> `` ta_res ?TA (map_vars_term \<sigma> r)"
        by auto
    qed
    then show ?thesis
      unfolding rule_state_compatible_def by simp
  qed
qed

lemma rfc_rule_automaton_closed_impl_semantic:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_rule_automaton_closed_impl TAi qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and i_le: "i \<le> length lw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and p_state: "p \<in> ta_states (ta_of TAi)"
    and lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term lw ''x'')))"
  shows "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
proof -
  have lhs_split: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q)
        (lift_term 0 (rfc_word_term (take i lw @ drop i lw) ''x'')))"
    using lhs i_le by simp
  from lhs_split
  obtain m where suffix: "m \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop i lw) ''x'')))"
    and prefix: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    by (rule rfc_word_ta_res_appendE)
  have m_state: "m \<in> ta_states (ta_of TAi)"
    using q_state suffix by (rule rfc_word_ta_res_state)
  have qs_q: "q \<in> set qs" using state_cover q_state by blast
  have qs_m: "m \<in> set qs" using state_cover m_state by blast
  have qs_p: "p \<in> set qs" using state_cover p_state by blast
  have suffix_impl: "rfc_word_reaches_impl TAi q (drop i lw) m"
    by (rule rfc_word_reaches_impl_complete[OF inv suffix])
  have prefix_impl: "rfc_word_reaches_impl TAi m (take i lw) p"
    by (rule rfc_word_reaches_impl_complete[OF inv prefix])
  have "rfc_word_reaches_impl TAi q rw p"
    by (rule rfc_rule_automaton_closed_implD[
        OF closed words i qs_q qs_m qs_p suffix_impl prefix_impl])
  then show ?thesis
    by (rule rfc_word_reaches_impl_sound[OF inv])
qed

lemma rfc_word_term_replicate_poss:
  "replicate i 0 \<in> poss (rfc_word_term w x) \<longleftrightarrow> i \<le> length w"
proof (induct w arbitrary: i)
  case Nil
  then show ?case
    by (cases i) auto
next
  case (Cons f w)
  then show ?case
    by (cases i) auto
qed

lemma rfc_word_term_subt_at_replicate:
  assumes "i \<le> length w"
  shows "rfc_word_term w x |_ replicate i 0 = rfc_word_term (drop i w) x"
  using assms
proof (induct w arbitrary: i)
  case Nil
  then show ?case
    by (cases i) auto
next
  case (Cons f w)
  then show ?case
    by (cases i) auto
qed

lemma rfc_word_term_is_Fun_subt_at_replicate:
  assumes "i < length w"
  shows "is_Fun (rfc_word_term w x |_ replicate i 0)"
  using rfc_word_term_subt_at_replicate[of i w x] assms
  by (cases "drop i w") auto

lemma rfc_word_term_poss_fun_replicate:
  assumes p: "p \<in> poss (rfc_word_term w x)"
    and isfun: "is_Fun (rfc_word_term w x |_ p)"
  shows "\<exists>i<length w. p = replicate i 0"
  using p isfun
proof (induct w arbitrary: p)
  case Nil
  then show ?case by auto
next
  case (Cons f w)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis by auto
  next
    case (Cons j ps)
    with Cons.prems have j: "j = 0" and ps: "ps \<in> poss (rfc_word_term w x)"
      by auto
    from Cons.prems Cons have fun_ps: "is_Fun (rfc_word_term w x |_ ps)"
      unfolding j by (cases ps) auto
    from Cons.hyps[OF ps fun_ps] obtain i where i: "i < length w" and ps_rep: "ps = replicate i 0"
      by blast
    show ?thesis
      unfolding Cons j ps_rep by (intro exI[of _ "Suc i"]) (simp add: i)
  qed
qed

lemma rfc_word_term_replace_at_replicate:
  assumes "i \<le> length w"
  shows "replace_at (rfc_word_term w x) (replicate i 0) (rfc_word_term v y) =
    rfc_word_term (take i w @ v) y"
  using assms
proof (induct w arbitrary: i)
  case Nil
  then show ?case
    by (cases i) auto
next
  case (Cons f w)
  then show ?case
    by (cases i) auto
qed

lemma rfc_word_term_subst_eq_prefix_cases:
  assumes "rfc_word_term v x \<cdot> \<sigma> = rfc_word_term w y \<cdot> \<tau>"
  shows "(\<exists>rest. w = v @ rest \<and> \<sigma> x = rfc_word_term rest y \<cdot> \<tau>) \<or>
    (\<exists>rest. v = w @ rest \<and> \<tau> y = rfc_word_term rest x \<cdot> \<sigma>)"
  using assms
proof (induct v arbitrary: w)
  case Nil
  then show ?case by auto
next
  case (Cons f v)
  show ?case
  proof (cases w)
    case Nil
    with Cons.prems show ?thesis by auto
  next
    case (Cons g ws)
    from Cons.prems Cons have fg: "f = g"
      by auto
    from Cons.prems Cons fg have eq: "rfc_word_term v x \<cdot> \<sigma> = rfc_word_term ws y \<cdot> \<tau>"
      by auto
    from Cons.hyps[OF eq] show ?thesis
    proof
      assume "\<exists>rest. ws = v @ rest \<and> \<sigma> x = rfc_word_term rest y \<cdot> \<tau>"
      then obtain rest where rest: "ws = v @ rest"
        and subst: "\<sigma> x = rfc_word_term rest y \<cdot> \<tau>"
        by auto
      show ?thesis
        using rest subst Cons fg by auto
    next
      assume "\<exists>rest. v = ws @ rest \<and> \<tau> y = rfc_word_term rest x \<cdot> \<sigma>"
      then obtain rest where rest: "v = ws @ rest"
        and subst: "\<tau> y = rfc_word_term rest x \<cdot> \<sigma>"
        by auto
      show ?thesis
        using rest subst Cons fg by auto
    qed
  qed
qed

lemma rfc_automaton_closed_impl_rule:
  assumes closed: "rfc_automaton_closed_impl TA qs R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_automaton_closed_impl TA qs lr"
  using assms unfolding rfc_automaton_closed_impl_def
  by (auto simp: list_all_iff)

lemma rfc_automaton_closed_impl_rule_words:
  assumes closed: "rfc_automaton_closed_impl TA qs R"
    and lr: "lr \<in> set R"
  shows "\<exists>lw rw. rfc_rule_words lr = Some (lw, rw)"
proof -
  from rfc_automaton_closed_impl_rule[OF closed lr]
  show ?thesis
    unfolding rfc_rule_automaton_closed_impl_def
    by (cases "rfc_rule_words lr") auto
qed

lemma rfc_automaton_closed_impl_rhss_word:
  assumes closed: "rfc_automaton_closed_impl TA qs R"
    and r: "r \<in> rhss (set R)"
  shows "\<exists>w x. r = rfc_word_term w x"
proof -
  from r obtain l where lr: "(l,r) \<in> set R"
    by auto
  from rfc_automaton_closed_impl_rule_words[OF closed lr]
  obtain lw rw where words: "rfc_rule_words (l,r) = Some (lw,rw)"
    by auto
  from rfc_rule_words_sound[OF words]
  show ?thesis by auto
qed

lemma rfc_initial_accepted_rhss:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and covers: "rfc_initial_covers R I"
    and acc: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TAi qfin I"
    and t: "t \<in> rhss (set R)"
    and q: "q \<in> set qfin"
  shows "\<exists>qf\<in>ta_final (ta_of TAi).
    qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from rfc_initial_covers[OF covers] t have tI: "t \<in> set I"
    by auto
  from rfc_initial_accepted_with_tail_states_impl[OF inv acc tI q]
  show ?thesis .
qed

lemma rfc_initial_paired_accepted_impl_nth:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and acc: "rfc_initial_paired_accepted_impl TYPE('f) TAi tails I"
    and i: "i < length I"
  shows "\<exists>qf\<in>ta_final (ta_of TAi).
    qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. tails ! i) (lift_term 0 (I ! i)))"
proof -
  from acc have len: "length tails = length I"
    and all: "list_all (\<lambda>(t,q).
      rfc_term_accepted_with_tail_states_impl TYPE('f) TAi [q] t)
      (zip I tails)"
    unfolding rfc_initial_paired_accepted_impl_def by auto
  have iz: "i < length (zip I tails)"
    using i len by simp
  have pair: "(I ! i, tails ! i) \<in> set (zip I tails)"
    using nth_mem[OF iz] i len by simp
  from list_all_member[OF all pair]
  have term_acc:
    "rfc_term_accepted_with_tail_states_impl TYPE('f) TAi [tails ! i] (I ! i)"
    by simp
  from rfc_term_accepted_with_tail_states_impl[OF inv term_acc]
  show ?thesis by simp
qed

lemma rfc_initial_paired_accepted_rhss:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and covers: "rfc_initial_covers R I"
    and acc: "rfc_initial_paired_accepted_impl TYPE('f) TAi tails I"
    and lr: "(l,r) \<in> set R"
  shows "\<exists>q\<in>set tails. \<exists>qf\<in>ta_final (ta_of TAi).
    qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 r))"
proof -
  from lr have r_rhs: "r \<in> rhss (set R)" by auto
  from rfc_initial_covers[OF covers] r_rhs have rI: "r \<in> set I" by auto
  from rI obtain i where iI: "i < length I" and nthI: "I ! i = r"
    unfolding in_set_conv_nth by blast
  have len: "length tails = length I"
    using acc unfolding rfc_initial_paired_accepted_impl_def by auto
  have q: "tails ! i \<in> set tails"
    using iI len by auto
  from rfc_initial_paired_accepted_impl_nth[OF inv acc iI]
  show ?thesis using q unfolding nthI by blast
qed

lemma rfc_matchbox_closed_impl_rule:
  assumes closed: "rfc_matchbox_closed_impl TA rel qs R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_matchbox_closed_impl TA rel qs lr"
  using assms unfolding rfc_matchbox_closed_impl_def
  by (auto simp: list_all_iff)

lemma rfc_matchbox_closed_impl_rule_words:
  assumes closed: "rfc_matchbox_closed_impl TA rel qs R"
    and lr: "lr \<in> set R"
  shows "\<exists>lw rw. rfc_rule_words lr = Some (lw, rw)"
proof -
  from rfc_matchbox_closed_impl_rule[OF closed lr]
  show ?thesis
    unfolding rfc_rule_matchbox_closed_impl_def
    by (cases "rfc_rule_words lr") auto
qed

lemma rfc_matchbox_closed_impl_rhss_word:
  assumes closed: "rfc_matchbox_closed_impl TA rel qs R"
    and r: "r \<in> rhss (set R)"
  shows "\<exists>w x. r = rfc_word_term w x"
proof -
  from r obtain l where lr: "(l,r) \<in> set R"
    by auto
  from rfc_matchbox_closed_impl_rule_words[OF closed lr]
  obtain lw rw where words: "rfc_rule_words (l,r) = Some (lw,rw)"
    by auto
  from rfc_rule_words_sound[OF words]
  show ?thesis by auto
qed

lemma rfc_native_matchbox_closed_impl_rule:
  assumes closed: "rfc_native_matchbox_closed_impl TA rel qs R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_native_matchbox_closed_impl TA rel qs lr"
  using assms unfolding rfc_native_matchbox_closed_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_native_matchbox_closed_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and closed: "rfc_rule_native_matchbox_closed_impl TAi rel_info qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and q: "q \<in> set qs"
    and p: "p \<in> rfc_native_word_res (ta_of TAi) q 0 lw"
  shows "p \<in> (relation_of rel_info)\<inverse> ``
    rfc_native_word_res (ta_of TAi) q 0 rw"
proof -
  let ?lhs = "rfc_native_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 lw"
  let ?rhs = "rfc_native_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 rw"
  from closed words q have rel_ok:
    "rel_checker rel_info ?lhs ?rhs = None"
    unfolding rfc_rule_native_matchbox_closed_impl_def
    by (auto simp: list_all_iff)
  from rel_checker[OF rel_ok] have subset:
    "rs.\<alpha> ?lhs \<subseteq>
      (relation_of rel_info)\<inverse> `` rs.\<alpha> ?rhs" .
  have lhs: "rs.\<alpha> ?lhs =
      rfc_native_word_res (ta_of TAi) q 0 lw"
    by (rule rfc_native_word_res_impl_eq[OF inv])
  have rhs: "rs.\<alpha> ?rhs =
      rfc_native_word_res (ta_of TAi) q 0 rw"
    by (rule rfc_native_word_res_impl_eq[OF inv])
  from subset p lhs rhs show ?thesis by auto
qed

lemma rfc_rule_native_matchbox_closed_Id_imp:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_rule_native_matchbox_closed_impl
      TAi Id_Relation qs lr"
    and words: "rfc_rule_words lr = Some (lw,rw)"
    and lw_ne: "lw \<noteq> []"
  shows "rfc_rule_matchbox_closed_impl TAi Id_Relation qs lr"
proof -
  interpret ta_inv TAi "rel_checker Id_Relation" Id by (rule inv)
  let ?TA = "ta_of TAi"
  have target: "list_all (\<lambda>q.
      rel_checker Id_Relation
        (rfc_word_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
          q 0 lw)
        (rfc_word_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
          q 0 rw) = None) qs"
  proof (simp only: list_all_iff, intro ballI)
    fix q
    assume q: "q \<in> set qs"
    let ?lhs = "rfc_word_res_impl
      (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 lw"
    let ?rhs = "rfc_word_res_impl
      (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 rw"
    have lhs_alpha: "rs.\<alpha> ?lhs = ta_res ?TA
        (map_vars_term (\<lambda>_. q) (lift_term 0
          (rfc_word_term lw ''x'')))"
      by (simp add: rfc_word_res_impl_eq ta_res_impl)
    have rhs_alpha: "rs.\<alpha> ?rhs = ta_res ?TA
        (map_vars_term (\<lambda>_. q) (lift_term 0
          (rfc_word_term rw ''x'')))"
      by (simp add: rfc_word_res_impl_eq ta_res_impl)
    have subset: "rs.\<alpha> ?lhs \<subseteq> rs.\<alpha> ?rhs"
    proof
      fix p
      assume p: "p \<in> rs.\<alpha> ?lhs"
      from p[unfolded lhs_alpha]
        rfc_native_labeled_word_res_ta_res[
          of p ?TA q "map (\<lambda>f. (f,0)) lw"]
      obtain q0 p0 where
        q0: "q0 \<in> (ta_eps ?TA)\<^sup>* `` {q}"
        and p0: "p0 \<in> rfc_native_labeled_word_res ?TA q0
          (map (\<lambda>f. (f,0)) lw)"
        and p0p: "(p0,p) \<in> (ta_eps ?TA)\<^sup>*"
        unfolding lift_term_rfc_word_term by auto
      have q0_state: "q0 \<in> ta_states ?TA"
        using rfc_native_labeled_word_res_states[
          OF _ p0] lw_ne by auto
      have q0_qs: "q0 \<in> set qs"
        using state_cover q0_state by auto
      have inv': "ta_inv TAi (rel_checker Id_Relation)
          (relation_of Id_Relation)"
        using inv by simp
      have p0_rhs_rel: "p0 \<in> (relation_of Id_Relation)\<inverse> ``
          rfc_native_word_res ?TA q0 0 rw"
        by (rule rfc_rule_native_matchbox_closed_implD[
          OF inv' closed words q0_qs])
          (use p0 in \<open>simp add: rfc_native_labeled_word_res_uniform\<close>)
      have p0_rhs: "p0 \<in> rfc_native_word_res ?TA q0 0 rw"
        using p0_rhs_rel by simp
      have p_rhs: "p \<in> ta_res ?TA
          (map_vars_term (\<lambda>_. q) (lift_term 0
            (rfc_word_term rw ''x'')))"
        using rfc_native_labeled_word_res_ta_res[
          of p ?TA q "map (\<lambda>f. (f,0)) rw"]
          q0 p0_rhs p0p
        unfolding rfc_native_labeled_word_res_uniform
          lift_term_rfc_word_term
        by auto
      show "p \<in> rs.\<alpha> ?rhs"
        using p_rhs rhs_alpha by simp
    qed
    show "rel_checker Id_Relation ?lhs ?rhs = None"
      using subset by (simp add: rs_\<alpha>_to_RBT_keys)
  qed
  show ?thesis
    using target unfolding rfc_rule_matchbox_closed_impl_def
    by (simp add: words)
qed

lemma rfc_native_matchbox_closed_Id_imp:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_native_matchbox_closed_impl
      TAi Id_Relation qs R"
    and wf: "wf_trs (set R)"
  shows "rfc_matchbox_closed_impl TAi Id_Relation qs R"
  unfolding rfc_matchbox_closed_impl_def list_all_iff
proof
  fix lr
  assume lr: "lr \<in> set R"
  from rfc_native_matchbox_closed_impl_rule[OF closed lr]
  have closed_lr: "rfc_rule_native_matchbox_closed_impl
      TAi Id_Relation qs lr" .
  then obtain lw rw where words: "rfc_rule_words lr = Some (lw,rw)"
    unfolding rfc_rule_native_matchbox_closed_impl_def
    by (cases "rfc_rule_words lr") auto
  from rfc_rule_words_sound[OF words] obtain x where
    lhs: "fst lr = rfc_word_term lw x"
    by auto
  have lw_ne: "lw \<noteq> []"
  proof
    assume "lw = []"
    then have "is_Var (fst lr)"
      using lhs by simp
    moreover have "\<exists>f ts. fst lr = Fun f ts"
      using wf lr unfolding wf_trs_def by (cases lr) auto
    then obtain f ts where "fst lr = Fun f ts" by blast
    then have "\<not> is_Var (fst lr)" by simp
    ultimately show False by simp
  qed
  show "rfc_rule_matchbox_closed_impl TAi Id_Relation qs lr"
    by (rule rfc_rule_native_matchbox_closed_Id_imp[
      OF inv state_cover closed_lr words lw_ne])
qed

lemma rfc_native_matchbox_ext_right_impl_rule:
  assumes ext: "rfc_native_matchbox_ext_right_impl TA rel tails R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_native_matchbox_ext_right_impl TA rel tails lr"
  using assms unfolding rfc_native_matchbox_ext_right_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_native_matchbox_ext_right_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and ext: "rfc_rule_native_matchbox_ext_right_impl TAi rel_info tails lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<length lw]"
    and q: "q \<in> set tails"
    and p: "p \<in> rfc_native_word_res (ta_of TAi) q 0 (take i lw)"
  shows "p \<in> (relation_of rel_info)\<inverse> ``
    rfc_native_word_res (ta_of TAi) q 0 rw"
proof -
  let ?lhs = "rfc_native_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 (take i lw)"
  let ?rhs = "rfc_native_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 rw"
  from ext words i q have rel_ok:
    "rel_checker rel_info ?lhs ?rhs = None"
    unfolding rfc_rule_native_matchbox_ext_right_impl_def
    by (auto simp: list_all_iff Let_def)
  from rel_checker[OF rel_ok] have subset:
    "rs.\<alpha> ?lhs \<subseteq>
      (relation_of rel_info)\<inverse> `` rs.\<alpha> ?rhs" .
  have lhs: "rs.\<alpha> ?lhs =
      rfc_native_word_res (ta_of TAi) q 0 (take i lw)"
    by (rule rfc_native_word_res_impl_eq[OF inv])
  have rhs: "rs.\<alpha> ?rhs =
      rfc_native_word_res (ta_of TAi) q 0 rw"
    by (rule rfc_native_word_res_impl_eq[OF inv])
  from subset p lhs rhs show ?thesis by auto
qed

lemma rfc_rule_native_matchbox_ext_right_Id_imp:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and ext: "rfc_rule_native_matchbox_ext_right_impl
      TAi Id_Relation qs lr"
    and words: "rfc_rule_words lr = Some (lw,rw)"
  shows "rfc_rule_matchbox_ext_right_impl
    TAi Id_Relation tails qs lr"
proof -
  interpret ta_inv TAi "rel_checker Id_Relation" Id by (rule inv)
  let ?TA = "ta_of TAi"
  from ext words have lw_ne: "lw \<noteq> []"
    unfolding rfc_rule_native_matchbox_ext_right_impl_def by simp
  have target: "list_all (\<lambda>q.
      let rhs = rfc_word_res_impl (ta_rules_impl TAi)
        (ta_epss_impl TAi) q 0 rw
      in list_all (\<lambda>i.
        let prefix = take i lw
        in rel_checker Id_Relation
          (rfc_word_res_impl (ta_rules_impl TAi)
            (ta_epss_impl TAi) q 0 prefix) rhs = None)
        [1..<length lw]) tails"
  proof (simp only: list_all_iff Let_def, rule ballI)
    fix q
    assume q_tail: "q \<in> set tails"
    show "\<forall>i\<in>set [1..<length lw].
      rel_checker Id_Relation
        (rfc_word_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
          q 0 (take i lw))
        (rfc_word_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
          q 0 rw) = None"
    proof (intro ballI)
      fix i
      assume i: "i \<in> set [1..<length lw]"
      let ?lhs = "rfc_word_res_impl
        (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 (take i lw)"
      let ?rhs = "rfc_word_res_impl
        (ta_rules_impl TAi) (ta_epss_impl TAi) q 0 rw"
      have take_ne: "take i lw \<noteq> []"
        using i by auto
      have lhs_alpha: "rs.\<alpha> ?lhs = ta_res ?TA
          (map_vars_term (\<lambda>_. q) (lift_term 0
            (rfc_word_term (take i lw) ''x'')))"
        by (simp add: rfc_word_res_impl_eq ta_res_impl)
      have rhs_alpha: "rs.\<alpha> ?rhs = ta_res ?TA
          (map_vars_term (\<lambda>_. q) (lift_term 0
            (rfc_word_term rw ''x'')))"
        by (simp add: rfc_word_res_impl_eq ta_res_impl)
      have subset: "rs.\<alpha> ?lhs \<subseteq> rs.\<alpha> ?rhs"
      proof
        fix p
        assume p: "p \<in> rs.\<alpha> ?lhs"
        from p[unfolded lhs_alpha]
          rfc_native_labeled_word_res_ta_res[
            of p ?TA q "map (\<lambda>f. (f,0)) (take i lw)"]
        obtain q0 p0 where
          q0: "q0 \<in> (ta_eps ?TA)\<^sup>* `` {q}"
          and p0: "p0 \<in> rfc_native_labeled_word_res ?TA q0
            (map (\<lambda>f. (f,0)) (take i lw))"
          and p0p: "(p0,p) \<in> (ta_eps ?TA)\<^sup>*"
          unfolding lift_term_rfc_word_term by auto
        have q0_state: "q0 \<in> ta_states ?TA"
          using rfc_native_labeled_word_res_states[
            OF _ p0] take_ne by auto
        have q0_qs: "q0 \<in> set qs"
          using state_cover q0_state by auto
        have inv': "ta_inv TAi (rel_checker Id_Relation)
            (relation_of Id_Relation)"
          using inv by simp
        have p0_rhs_rel: "p0 \<in> (relation_of Id_Relation)\<inverse> ``
            rfc_native_word_res ?TA q0 0 rw"
          by (rule rfc_rule_native_matchbox_ext_right_implD[
            OF inv' ext words i q0_qs])
            (use p0 in \<open>simp add: rfc_native_labeled_word_res_uniform\<close>)
        have p0_rhs: "p0 \<in> rfc_native_word_res ?TA q0 0 rw"
          using p0_rhs_rel by simp
        have p_rhs: "p \<in> ta_res ?TA
            (map_vars_term (\<lambda>_. q) (lift_term 0
              (rfc_word_term rw ''x'')))"
          using rfc_native_labeled_word_res_ta_res[
            of p ?TA q "map (\<lambda>f. (f,0)) rw"]
            q0 p0_rhs p0p
          unfolding rfc_native_labeled_word_res_uniform
            lift_term_rfc_word_term
          by auto
        show "p \<in> rs.\<alpha> ?rhs"
          using p_rhs rhs_alpha by simp
      qed
      show "rel_checker Id_Relation ?lhs ?rhs = None"
        using subset by (simp add: rs_\<alpha>_to_RBT_keys)
    qed
  qed
  show ?thesis
    using target lw_ne unfolding rfc_rule_matchbox_ext_right_impl_def
    by (simp add: words)
qed

lemma rfc_native_matchbox_ext_right_Id_imp:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and ext: "rfc_native_matchbox_ext_right_impl
      TAi Id_Relation qs R"
  shows "rfc_matchbox_ext_right_impl
    TAi Id_Relation tails qs R"
  unfolding rfc_matchbox_ext_right_impl_def list_all_iff
proof
  fix lr
  assume lr: "lr \<in> set R"
  from rfc_native_matchbox_ext_right_impl_rule[OF ext lr]
  have ext_lr: "rfc_rule_native_matchbox_ext_right_impl
      TAi Id_Relation qs lr" .
  then obtain lw rw where words: "rfc_rule_words lr = Some (lw,rw)"
    unfolding rfc_rule_native_matchbox_ext_right_impl_def
    by (cases "rfc_rule_words lr") auto
  show "rfc_rule_matchbox_ext_right_impl
      TAi Id_Relation tails qs lr"
    by (rule rfc_rule_native_matchbox_ext_right_Id_imp[
      OF inv state_cover ext_lr words])
qed

lemma rfc_native_no_top_redex_impl_rule:
  assumes no_top: "rfc_native_no_top_redex_impl TA qs c R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_native_no_top_redex_impl TA qs c lr"
  using assms unfolding rfc_native_no_top_redex_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_native_no_top_redex_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and no_top: "rfc_rule_native_no_top_redex_impl TAi qs c lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and q: "q \<in> set qs"
    and p: "p \<in> set qs"
  shows "p \<notin> rfc_native_word_res (ta_of TAi) q c lw"
proof -
  let ?res = "rfc_native_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q c lw"
  from no_top words q have empty:
    "rs.isEmpty (rs.inter (rs.from_list qs) ?res)"
    unfolding rfc_rule_native_no_top_redex_impl_def
    by (auto simp: list_all_iff Let_def)
  have impl: "p \<notin> rs.\<alpha> ?res"
    using empty p by (auto simp: rs.correct)
  have alpha: "rs.\<alpha> ?res =
      rfc_native_word_res (ta_of TAi) q c lw"
    by (rule rfc_native_word_res_impl_eq[OF inv])
  from impl alpha show ?thesis by simp
qed

lemma rfc_native_inner_splice_impl_rule:
  assumes splice: "rfc_native_inner_splice_impl TA qs c R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_native_inner_splice_impl TA qs c lr"
  using assms unfolding rfc_native_inner_splice_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_native_inner_splice_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and splice: "rfc_rule_native_inner_splice_impl TAi qs c lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and q: "q \<in> set qs"
    and labels: "lfhs \<in> set (rfc_labeled_height_vectors c lw)"
    and p: "p \<in> rfc_native_labeled_word_res (ta_of TAi) q lfhs"
  defines "h \<equiv> min c (Suc (rfc_labeled_min_height lfhs))"
  shows "p \<in> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (rfc_word_term (map (\<lambda>f. (f,h)) rw) ''x''))"
proof -
  interpret ta_inv TAi rel rell by (rule inv)
  let ?TA = "ta_of TAi"
  let ?lhs = "rfc_native_labeled_word_res_impl
    (ta_rules_impl TAi) (ta_epss_impl TAi) q lfhs"
  have p_impl: "p \<in> rs.\<alpha> ?lhs"
    using p rfc_native_labeled_word_res_impl_eq[OF inv, of q lfhs]
    by simp
  from splice words q labels p_impl have checked:
    "if rw = [] then rs.memb p (ta_epss_impl TAi q)
     else list_ex (\<lambda>s.
       let rhs = rfc_native_labeled_word_res_impl
         (ta_rules_impl TAi) (ta_epss_impl TAi) s
         (map (\<lambda>f. (f,h)) rw)
       in list_ex (\<lambda>e. rs.memb p (ta_epss_impl TAi e))
         (rs.to_list rhs))
       (rs.to_list (ta_epss_impl TAi q))"
    unfolding rfc_rule_native_inner_splice_impl_def h_def
    by (auto simp: list_all_iff Let_def rs.correct)
  show ?thesis
  proof (cases "rw = []")
    case True
    with checked have "(q,p) \<in> (ta_eps ?TA)\<^sup>*"
      by (simp add: ta_epss rs.correct)
    with True show ?thesis by simp
  next
    case False
    from checked False obtain s e where
      s_impl: "s \<in> set (rs.to_list (ta_epss_impl TAi q))"
      and e_impl: "e \<in> set (rs.to_list
        (rfc_native_labeled_word_res_impl
          (ta_rules_impl TAi) (ta_epss_impl TAi) s
          (map (\<lambda>f. (f,h)) rw)))"
      and ep_impl: "p \<in> set (rs.to_list (ta_epss_impl TAi e))"
      by (auto simp: Let_def list_ex_iff rs.correct)
    have qs: "(q,s) \<in> (ta_eps ?TA)\<^sup>*"
      using s_impl by (simp add: ta_epss rs.correct)
    have e: "e \<in> rfc_native_labeled_word_res ?TA s
        (map (\<lambda>f. (f,h)) rw)"
      using e_impl rfc_native_labeled_word_res_impl_eq[OF inv, of s
        "map (\<lambda>f. (f,h)) rw"]
      by (simp add: rs.correct)
    have ep: "(e,p) \<in> (ta_eps ?TA)\<^sup>*"
      using ep_impl by (simp add: ta_epss rs.correct)
    show ?thesis
      using rfc_native_labeled_word_res_ta_res[
        of p ?TA q "map (\<lambda>f. (f,h)) rw"] qs e ep
      by auto
  qed
qed

lemma rfc_rule_native_inner_splice_compatible:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and splice: "rfc_rule_native_inner_splice_impl TAi qs c lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and labels: "lfhs \<in> set (rfc_labeled_height_vectors c lw)"
  defines "h \<equiv> min c (Suc (rfc_labeled_min_height lfhs))"
  shows "rule_state_compatible (ta_of TAi) Id
    (rfc_word_term lfhs x, rfc_word_term (map (\<lambda>f. (f,h)) rw) x)"
proof -
  let ?TA = "ta_of TAi"
  from splice words have lw_ne: "lw \<noteq> []"
    unfolding rfc_rule_native_inner_splice_impl_def by simp
  have labels_ne: "lfhs \<noteq> []"
    using rfc_labeled_height_vectors_length[OF labels] lw_ne by auto
  show ?thesis
    unfolding rule_state_compatible_def
  proof (simp only: prod.case, intro allI impI subsetI)
    fix \<sigma> p
    assume sig: "\<sigma> ` vars_term (rfc_word_term lfhs x) \<subseteq>
        ta_rhs_states ?TA"
      and p: "p \<in> ta_res ?TA
        (map_vars_term \<sigma> (rfc_word_term lfhs x))"
    have vars: "vars_term (rfc_word_term lfhs x) = {x}"
      by (induct lfhs) auto
    have tail_rhs: "\<sigma> x \<in> ta_rhs_states ?TA"
      using sig vars by auto
    have tail_state: "\<sigma> x \<in> ta_states ?TA"
      using tail_rhs ta_rhs_states_subset_states[of ?TA] by blast
    have lhs_term: "map_vars_term \<sigma> (rfc_word_term lfhs x) =
        map_vars_term (\<lambda>_. \<sigma> x) (rfc_word_term lfhs ''x'')"
      by (induct lfhs) auto
    from p[unfolded lhs_term]
      rfc_native_labeled_word_res_ta_res[of p ?TA "\<sigma> x" lfhs]
    obtain q0 p0 where
      q0: "q0 \<in> (ta_eps ?TA)\<^sup>* `` {\<sigma> x}"
      and p0: "p0 \<in> rfc_native_labeled_word_res ?TA q0 lfhs"
      and p0p: "(p0,p) \<in> (ta_eps ?TA)\<^sup>*"
      by auto
    have q0_state: "q0 \<in> ta_states ?TA"
      using q0 tail_state by (auto intro: ta_eps_ta_states)
    have q0_qs: "q0 \<in> set qs"
      using state_cover q0_state by auto
    have rhs0: "p0 \<in> ta_res ?TA
        (map_vars_term (\<lambda>_. q0)
          (rfc_word_term (map (\<lambda>f. (f,h)) rw) ''x''))"
      by (rule rfc_rule_native_inner_splice_implD[
        OF inv splice words q0_qs labels p0, folded h_def])
    from rhs0
      rfc_native_labeled_word_res_ta_res[
        of p0 ?TA q0 "map (\<lambda>f. (f,h)) rw"]
    obtain q1 e where
      q1: "q1 \<in> (ta_eps ?TA)\<^sup>* `` {q0}"
      and e: "e \<in> rfc_native_labeled_word_res ?TA q1
        (map (\<lambda>f. (f,h)) rw)"
      and ep0: "(e,p0) \<in> (ta_eps ?TA)\<^sup>*"
      by auto
    have tail_q1: "q1 \<in> (ta_eps ?TA)\<^sup>* `` {\<sigma> x}"
      using q0 q1 by (auto dest: rtrancl_trans)
    have rhs_p0: "p0 \<in> ta_res ?TA
        (map_vars_term (\<lambda>_. \<sigma> x)
          (rfc_word_term (map (\<lambda>f. (f,h)) rw) ''x''))"
      using rfc_native_labeled_word_res_ta_res[
        of p0 ?TA "\<sigma> x" "map (\<lambda>f. (f,h)) rw"]
        tail_q1 e ep0
      by auto
    have rhs_term: "map_vars_term (\<lambda>_. \<sigma> x)
          (rfc_word_term (map (\<lambda>f. (f,h)) rw) ''x'') =
        map_vars_term \<sigma> (rfc_word_term (map (\<lambda>f. (f,h)) rw) x)"
      by (induct rw) auto
    have "p \<in> ta_res ?TA
        (map_vars_term \<sigma> (rfc_word_term (map (\<lambda>f. (f,h)) rw) x))"
      using ta_res_eps[OF rhs_p0 p0p] unfolding rhs_term .
    then show "p \<in> Id\<inverse> ``
        ta_res ?TA
          (map_vars_term \<sigma> (rfc_word_term (map (\<lambda>f. (f,h)) rw) x))"
      by simp
  qed
qed

lemma rfc_native_inner_splice_full_strict_compat:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and splice: "rfc_native_inner_splice_impl TAi qs c R"
    and no_top: "rfc_native_no_top_redex_impl TAi qs c R"
  shows "state_compatible (ta_of TAi) Id
    (cover_bound c Matchbounds.match Strict_TRS (set R))"
proof (unfold state_compatible_def, intro allI impI)
  fix l r
  let ?TA = "ta_of TAi"
  assume lr: "(l,r) \<in> cover_bound c Matchbounds.match Strict_TRS (set R)"
    and funas: "funas_term l \<subseteq> ta_syms ?TA"
  have lr_cover:
    "(l,r) \<in> cover Matchbounds.match Strict_TRS (set R)"
    using lr unfolding cover_bound_def by auto
  have lr_bound: "\<And>fh n. (fh,n) \<in> funas_term l \<Longrightarrow>
      height fh \<le> c"
    using lr unfolding cover_bound_def by blast
  from lr_cover obtain bl br h where
    base_lr: "(bl,br) \<in> set R"
    and base_l: "base_term l = bl"
    and r: "r = lift_term h br"
    and h: "h = Suc (min_list (map height (funs_term_list l)))"
    unfolding cover_def
    by (auto simp: sym_collect_match)
  note bound = lr_bound
  from rfc_native_inner_splice_impl_rule[OF splice base_lr]
  have splice_rule: "rfc_rule_native_inner_splice_impl TAi qs c (bl,br)" .
  from splice_rule obtain lw rw where
    words: "rfc_rule_words (bl,br) = Some (lw,rw)"
    unfolding rfc_rule_native_inner_splice_impl_def
    by (cases "rfc_rule_words (bl,br)") auto
  from rfc_rule_words_sound[OF words] obtain x where
    bl: "bl = rfc_word_term lw x"
    and br: "br = rfc_word_term rw x"
    by auto
  from base_term_rfc_word_termE[OF base_l[unfolded bl]]
  obtain fhs where
    l: "l = rfc_word_term fhs x"
    and bases: "map fst fhs = lw"
    by auto
  from splice_rule words have lw_ne: "lw \<noteq> []"
    unfolding rfc_rule_native_inner_splice_impl_def by simp
  have fhs_ne: "fhs \<noteq> []"
    using bases lw_ne by auto
  have fhs_bound: "\<And>fh. fh \<in> set fhs \<Longrightarrow> snd fh \<le> c"
  proof -
    fix fh
    assume fh: "fh \<in> set fhs"
    have "(fh,1) \<in> funas_term l"
      unfolding l funas_term_rfc_word_term using fh by auto
    from bound[OF this] show "snd fh \<le> c"
      by (cases fh) simp
  qed
  have labels: "fhs \<in> set (rfc_labeled_height_vectors c lw)"
    by (rule rfc_labeled_height_vectors_complete[OF bases fhs_bound])
  let ?m = "min_list (map snd fhs)"
  have min_eq: "rfc_labeled_min_height fhs = ?m"
    by (rule rfc_labeled_min_height_min_list[OF fhs_ne])
  have funs: "funs_term_list l = fhs"
    unfolding l by simp
  have heights: "map height fhs = map snd fhs"
    by (induct fhs) (auto split: prod.splits)
  have h_eq: "h = Suc ?m"
    using h unfolding funs heights by simp
  have min_mem: "?m \<in> set (map snd fhs)"
    using min_list_ex[of "map snd fhs"] fhs_ne by auto
  have min_le_c: "?m \<le> c"
    using min_mem fhs_bound by auto
  show "rule_state_compatible ?TA Id (l,r)"
  proof (cases "?m < c")
    case True
    have native_h: "min c (Suc (rfc_labeled_min_height fhs)) = h"
      using True h_eq min_eq by simp
    have compat: "rule_state_compatible ?TA Id
      (rfc_word_term fhs x,
       rfc_word_term (map (\<lambda>f. (f,min c
         (Suc (rfc_labeled_min_height fhs)))) rw) x)"
      by (rule rfc_rule_native_inner_splice_compatible[
        OF inv state_cover splice_rule words labels])
    show ?thesis
      using compat unfolding l r br lift_term_rfc_word_term native_h .
  next
    case False
    have min_c: "?m = c"
      using False min_le_c by simp
    have all_c: "\<And>fh. fh \<in> set fhs \<Longrightarrow> snd fh = c"
    proof -
      fix fh
      assume fh: "fh \<in> set fhs"
      have "?m \<le> snd fh"
        by (rule min_list) (use fh in auto)
      with fhs_bound[OF fh] show "snd fh = c"
        unfolding min_c by simp
    qed
    have uniform0: "map (\<lambda>fh. (fst fh,c)) fhs = fhs"
      by (rule map_idI, insert all_c, case_tac x, auto)
    have uniform: "fhs = map (\<lambda>f. (f,c)) lw"
    proof -
      have mapped:
        "map (\<lambda>f. (f,c)) (map fst fhs) =
          map (\<lambda>f. (f,c)) lw"
        by (rule arg_cong[OF bases])
      have compose:
        "map ((\<lambda>f. (f,c)) \<circ> fst) fhs =
          map (\<lambda>fh. (fst fh,c)) fhs"
        by (induct fhs) auto
      have "map (\<lambda>f. (f,c)) lw =
          map (\<lambda>fh. (fst fh,c)) fhs"
        using mapped[symmetric] compose by (simp only: map_map)
      also have "... = fhs" by (rule uniform0)
      finally show ?thesis by simp
    qed
    from rfc_native_no_top_redex_impl_rule[OF no_top base_lr]
    have no_top_rule: "rfc_rule_native_no_top_redex_impl TAi qs c (bl,br)" .
    show ?thesis
      unfolding rule_state_compatible_def
    proof (simp only: prod.case, intro allI impI subsetI)
      fix \<sigma> p
      assume sig: "\<sigma> ` vars_term l \<subseteq> ta_rhs_states ?TA"
        and p: "p \<in> ta_res ?TA (map_vars_term \<sigma> l)"
      have vars: "vars_term l = {x}"
        unfolding l by (induct fhs) auto
      have tail_rhs: "\<sigma> x \<in> ta_rhs_states ?TA"
        using sig vars by auto
      have tail_state: "\<sigma> x \<in> ta_states ?TA"
        using tail_rhs ta_rhs_states_subset_states[of ?TA] by blast
      have lhs_term: "map_vars_term \<sigma> l =
          map_vars_term (\<lambda>_. \<sigma> x)
            (rfc_word_term fhs ''x'')"
        unfolding l by (induct fhs) auto
      from p[unfolded lhs_term]
        rfc_native_labeled_word_res_ta_res[of p ?TA "\<sigma> x" fhs]
      obtain q0 p0 where
        q0: "q0 \<in> (ta_eps ?TA)\<^sup>* `` {\<sigma> x}"
        and p0: "p0 \<in> rfc_native_labeled_word_res ?TA q0 fhs"
        and p0p: "(p0,p) \<in> (ta_eps ?TA)\<^sup>*"
        by auto
      have q0_state: "q0 \<in> ta_states ?TA"
        using q0 tail_state by (auto intro: ta_eps_ta_states)
      have q0_qs: "q0 \<in> set qs"
        using state_cover q0_state by auto
      have p0_res: "p0 \<in> ta_res ?TA
          (map_vars_term (\<lambda>_. q0) (lift_term c
            (rfc_word_term lw ''x'')))"
        using rfc_native_labeled_word_res_ta_res[
          of p0 ?TA q0 "map (\<lambda>f. (f,c)) lw"]
          p0 unfolding uniform lift_term_rfc_word_term
        by auto
      have p0_state: "p0 \<in> ta_states ?TA"
        by (rule rfc_word_ta_res_state_height[OF q0_state p0_res])
      have p0_qs: "p0 \<in> set qs"
        using state_cover p0_state by auto
      have "p0 \<notin> rfc_native_word_res ?TA q0 c lw"
        by (rule rfc_rule_native_no_top_redex_implD[
          OF inv no_top_rule words q0_qs p0_qs])
      moreover have "p0 \<in> rfc_native_word_res ?TA q0 c lw"
        using p0 unfolding uniform rfc_native_labeled_word_res_uniform .
      ultimately show "p \<in> Id\<inverse> ``
          ta_res ?TA (map_vars_term \<sigma> r)"
        by contradiction
    qed
  qed
qed

lemma rfc_rule_matchbox_closed_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and closed: "rfc_rule_matchbox_closed_impl TAi rel_info qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and q: "q \<in> set qs"
    and m: "m \<in> set qs"
    and p: "p \<in> set qs"
    and suffix: "rfc_word_reaches_impl TAi q (drop i lw) m"
    and prefix: "rfc_word_reaches_impl TAi m (take i lw) p"
  shows "p \<in> (relation_of rel_info)\<inverse> `` ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
proof -
  let ?lhs_impl = "ta_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term lw ''x'')))"
  let ?rhs_impl = "ta_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
  from closed words q
  have rel_ok: "rel_checker rel_info ?lhs_impl ?rhs_impl = None"
    unfolding rfc_rule_matchbox_closed_impl_def
    by (auto simp: list_all_iff)
  from rel_checker[OF rel_ok]
  have subset: "rs.\<alpha> ?lhs_impl \<subseteq>
    (relation_of rel_info)\<inverse> `` rs.\<alpha> ?rhs_impl" .
  have full: "rfc_word_reaches_impl TAi q lw p"
    using rfc_word_reaches_impl_append[OF inv suffix prefix] i by simp
  have p_lhs: "p \<in> rs.\<alpha> ?lhs_impl"
    using full unfolding rfc_word_reaches_impl_def
    by (simp add: rs.correct)
  have rhs_eq: "rs.\<alpha> ?rhs_impl =
    ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
  proof -
    interpret ta_inv TAi "rel_checker rel_info" "relation_of rel_info"
      by (rule inv)
    show ?thesis
      by (simp add: ta_res_impl rs.correct)
  qed
  from subset p_lhs rhs_eq show ?thesis
    by auto
qed

lemma rfc_matchbox_ext_right_impl_rule:
  assumes ext: "rfc_matchbox_ext_right_impl TA rel tails qs R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_matchbox_ext_right_impl TA rel tails qs lr"
  using assms unfolding rfc_matchbox_ext_right_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_matchbox_ext_right_impl_words:
  assumes ext: "rfc_rule_matchbox_ext_right_impl TA rel tails qs lr"
  shows "\<exists>lw rw. rfc_rule_words lr = Some (lw, rw) \<and> lw \<noteq> []"
  using assms unfolding rfc_rule_matchbox_ext_right_impl_def
  by (cases "rfc_rule_words lr") auto

lemma rfc_matchbox_ext_right_impl_rule_words:
  assumes ext: "rfc_matchbox_ext_right_impl TA rel tails qs R"
    and lr: "lr \<in> set R"
  shows "\<exists>lw rw. rfc_rule_words lr = Some (lw, rw) \<and> lw \<noteq> []"
  by (rule rfc_rule_matchbox_ext_right_impl_words[
      OF rfc_matchbox_ext_right_impl_rule[OF ext lr]])

lemma rfc_rule_matchbox_ext_right_implD:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and ext: "rfc_rule_matchbox_ext_right_impl TAi rel_info tails qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<length lw]"
    and q: "q \<in> set tails"
    and p: "p \<in> set qs"
    and prefix: "rfc_word_reaches_impl TAi q (take i lw) p"
  shows "p \<in> (relation_of rel_info)\<inverse> `` ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
proof -
  let ?lhs_impl = "ta_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
    (map_vars_term (\<lambda>_. q)
      (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
  let ?rhs_impl = "ta_res_impl (ta_rules_impl TAi) (ta_epss_impl TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
  from ext words i q p prefix
  have rel_ok: "rel_checker rel_info ?lhs_impl ?rhs_impl = None"
    unfolding rfc_rule_matchbox_ext_right_impl_def
    by (auto simp: list_all_iff Let_def)
  from rel_checker[OF rel_ok]
  have subset: "rs.\<alpha> ?lhs_impl \<subseteq>
    (relation_of rel_info)\<inverse> `` rs.\<alpha> ?rhs_impl" .
  have p_lhs: "p \<in> rs.\<alpha> ?lhs_impl"
    using prefix unfolding rfc_word_reaches_impl_def
    by (simp add: rs.correct)
  have rhs_eq: "rs.\<alpha> ?rhs_impl =
    ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
  proof -
    interpret ta_inv TAi "rel_checker rel_info" "relation_of rel_info"
      by (rule inv)
    show ?thesis
      by (simp add: ta_res_impl rs.correct)
  qed
  from subset p_lhs rhs_eq show ?thesis
    by auto
qed

lemma rfc_rule_matchbox_closed_impl_semantic_context:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_rule_matchbox_closed_impl TAi rel_info qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and i_le: "i \<le> length lw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and p_state: "p \<in> ta_states (ta_of TAi)"
    and qf_state: "qf \<in> ta_states (ta_of TAi)"
    and suffix: "m \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop i lw) ''x'')))"
    and prefix_lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    and prefix_context: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term pre ''x'')))"
  shows "\<exists>qf'. (qf,qf') \<in> relation_of rel_info \<and>
    qf' \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
proof -
  let ?TA = "ta_of TAi"
  have m_state: "m \<in> ta_states ?TA"
    using q_state suffix by (rule rfc_word_ta_res_state)
  have qs_q: "q \<in> set qs" using state_cover q_state by blast
  have qs_m: "m \<in> set qs" using state_cover m_state by blast
  have qs_p: "p \<in> set qs" using state_cover p_state by blast
  have suffix_impl: "rfc_word_reaches_impl TAi q (drop i lw) m"
    by (rule rfc_word_reaches_impl_complete[OF inv suffix])
  have prefix_impl: "rfc_word_reaches_impl TAi m (take i lw) p"
    by (rule rfc_word_reaches_impl_complete[OF inv prefix_lhs])
  from rfc_rule_matchbox_closed_implD[
      OF inv closed words i qs_q qs_m qs_p suffix_impl prefix_impl]
  obtain p' where pp': "(p,p') \<in> relation_of rel_info"
    and rhs: "p' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
    by auto
  have prefix_context_ctxt: "qf \<in> ta_res ?TA ((rfc_word_ctxt pre)\<langle>Var p\<rangle>)"
    using prefix_context rfc_word_ctxt_apply[of pre p "''x''"] by simp
  from state_coherent_ctxt[OF coh pp' prefix_context_ctxt]
  obtain qf' where qfqf': "(qf,qf') \<in> relation_of rel_info"
    and ctxt_raw: "qf' \<in> ta_res ?TA ((rfc_word_ctxt pre)\<langle>Var p'\<rangle>)"
    by blast
  have ctxt: "qf' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. p') (lift_term 0 (rfc_word_term pre ''x'')))"
    using ctxt_raw rfc_word_ctxt_apply[of pre p' "''x''"] by simp
  have target: "qf' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
    by (rule rfc_word_ta_res_append[OF rhs ctxt])
  show ?thesis
    using qfqf' target by blast
qed

lemma rfc_rule_matchbox_ext_right_impl_semantic_context:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and ext: "rfc_rule_matchbox_ext_right_impl TAi rel_info tails qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<length lw]"
    and q_tail: "q \<in> set tails"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and p_state: "p \<in> ta_states (ta_of TAi)"
    and qf_state: "qf \<in> ta_states (ta_of TAi)"
    and prefix_lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    and prefix_context: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term pre ''x'')))"
  shows "\<exists>qf'. (qf,qf') \<in> relation_of rel_info \<and>
    qf' \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
proof -
  let ?TA = "ta_of TAi"
  have qs_p: "p \<in> set qs" using state_cover p_state by blast
  have prefix_impl: "rfc_word_reaches_impl TAi q (take i lw) p"
    by (rule rfc_word_reaches_impl_complete[OF inv prefix_lhs])
  from rfc_rule_matchbox_ext_right_implD[
      OF inv ext words i q_tail qs_p prefix_impl]
  obtain p' where pp': "(p,p') \<in> relation_of rel_info"
    and rhs: "p' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
    by auto
  have prefix_context_ctxt: "qf \<in> ta_res ?TA ((rfc_word_ctxt pre)\<langle>Var p\<rangle>)"
    using prefix_context rfc_word_ctxt_apply[of pre p "''x''"] by simp
  from state_coherent_ctxt[OF coh pp' prefix_context_ctxt]
  obtain qf' where qfqf': "(qf,qf') \<in> relation_of rel_info"
    and ctxt_raw: "qf' \<in> ta_res ?TA ((rfc_word_ctxt pre)\<langle>Var p'\<rangle>)"
    by blast
  have ctxt: "qf' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. p') (lift_term 0 (rfc_word_term pre ''x'')))"
    using ctxt_raw rfc_word_ctxt_apply[of pre p' "''x''"] by simp
  have target: "qf' \<in> ta_res ?TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
    by (rule rfc_word_ta_res_append[OF rhs ctxt])
  show ?thesis
    using qfqf' target by blast
qed

lemma rfc_rule_automaton_closed_impl_semantic_context:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_rule_automaton_closed_impl TAi qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and i_le: "i \<le> length lw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and p_state: "p \<in> ta_states (ta_of TAi)"
    and qf_state: "qf \<in> ta_states (ta_of TAi)"
    and suffix: "m \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop i lw) ''x'')))"
    and prefix_lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    and prefix_context: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term pre ''x'')))"
  shows "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
proof -
  have m_state: "m \<in> ta_states (ta_of TAi)"
    using q_state suffix by (rule rfc_word_ta_res_state)
  have lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term lw ''x'')))"
  proof -
    have "take i lw @ drop i lw = lw"
      by simp
    then show ?thesis
      using rfc_word_ta_res_append[OF suffix prefix_lhs] by simp
  qed
  have rhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
    by (rule rfc_rule_automaton_closed_impl_semantic[
        OF inv state_cover closed words i i_le q_state p_state lhs])
  from rfc_word_ta_res_append[OF rhs prefix_context]
  show ?thesis .
qed

lemma rfc_forward_closure_accepted_if_step_closed:
  assumes covers: "rfc_initial_covers R I"
    and initial_acc: "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> Q \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    and step_acc: "\<And>s u q. (\<And>q. q \<in> Q \<Longrightarrow>
        \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 s))) \<Longrightarrow>
      (s,u) \<in> rfc_narrow_step R \<Longrightarrow> q \<in> Q \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 u))"
    and t: "t \<in> rfc_forward_closure R"
    and q: "q \<in> Q"
  shows "\<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from t obtain s where s: "s \<in> rhss (set R)"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    unfolding rfc_forward_closure_def by auto
  have s_acc: "\<And>q. q \<in> Q \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 s))"
  proof -
    fix q
    assume "q \<in> Q"
    from rfc_initial_covers[OF covers] s have "s \<in> set I" by auto
    from initial_acc[OF this \<open>q \<in> Q\<close>]
    show "\<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 s))" .
  qed
  have all_acc: "\<And>q. q \<in> Q \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    using steps
  proof (induct)
    case base
    then show ?case using s_acc by blast
  next
    case step
    then show ?case using step_acc by blast
  qed
  from all_acc[OF q] show ?thesis .
qed

lemma rfc_automaton_closed_impl_split_accept:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed_all: "rfc_automaton_closed_impl TAi qs R"
    and lr: "lr \<in> set R"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and i_le: "i \<le> length lw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and suffix: "m \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop i lw) ''x'')))"
    and source_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ take i lw) ''x'')))"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
proof -
  have closed: "rfc_rule_automaton_closed_impl TAi qs lr"
    by (rule rfc_automaton_closed_impl_rule[OF closed_all lr])
  have m_state: "m \<in> ta_states (ta_of TAi)"
    using q_state suffix by (rule rfc_word_ta_res_state)
  from source_acc[OF m_state] obtain qf where qf_fin: "qf \<in> ta_final (ta_of TAi)"
    and qf_res: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (pre @ take i lw) ''x'')))"
    by auto
  from rfc_word_ta_res_appendE[OF qf_res]
  obtain p where prefix_lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    and prefix_context: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term pre ''x'')))"
    by blast
  have p_state: "p \<in> ta_states (ta_of TAi)"
    using m_state prefix_lhs by (rule rfc_word_ta_res_state)
  have qf_state: "qf \<in> ta_states (ta_of TAi)"
    using qf_fin unfolding ta_states_def by auto
  have "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
    by (rule rfc_rule_automaton_closed_impl_semantic_context[
        OF inv state_cover closed words i i_le q_state p_state qf_state suffix prefix_lhs prefix_context])
  with qf_fin show ?thesis
    by blast
qed

lemma rfc_word_reaches_some_implD:
  assumes some: "rfc_word_reaches_some_impl TA qs w q"
  obtains m where "m \<in> set qs" and "rfc_word_reaches_impl TA q w m"
  using some unfolding rfc_word_reaches_some_impl_def
  by (auto simp: list_all_iff)

lemma rfc_matchbox_closed_impl_split_accept:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed_all: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and lr: "lr \<in> set R"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<Suc (length lw)]"
    and i_le: "i \<le> length lw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and suffix: "m \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop i lw) ''x'')))"
    and source_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ take i lw) ''x'')))"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
proof -
  have closed: "rfc_rule_matchbox_closed_impl TAi rel_info qs lr"
    by (rule rfc_matchbox_closed_impl_rule[OF closed_all lr])
  have m_state: "m \<in> ta_states (ta_of TAi)"
    using q_state suffix by (rule rfc_word_ta_res_state)
  from source_acc[OF m_state] obtain qf where qf_fin: "qf \<in> ta_final (ta_of TAi)"
    and qf_res: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (pre @ take i lw) ''x'')))"
    by auto
  from rfc_word_ta_res_appendE[OF qf_res]
  obtain p where prefix_lhs: "p \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take i lw) ''x'')))"
    and prefix_context: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term pre ''x'')))"
    by blast
  have p_state: "p \<in> ta_states (ta_of TAi)"
    using m_state prefix_lhs by (rule rfc_word_ta_res_state)
  have qf_state: "qf \<in> ta_states (ta_of TAi)"
    using qf_fin unfolding ta_states_def by auto
  from rfc_rule_matchbox_closed_impl_semantic_context[
      OF inv state_cover coh closed words i i_le q_state p_state qf_state
        suffix prefix_lhs prefix_context]
  obtain qf' where qfqf': "(qf,qf') \<in> relation_of rel_info"
    and target: "qf' \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (pre @ rw) ''x'')))"
    by blast
  have qf'_fin: "qf' \<in> ta_final (ta_of TAi)"
    using state_coherentE2(1)[OF coh] qf_fin qfqf' by auto
  show ?thesis
    using qf'_fin target by blast
qed

lemma rfc_lhs_suffix_total_impl_rule:
  assumes total: "rfc_lhs_suffix_total_impl TA qs R"
    and lr: "lr \<in> set R"
  shows "rfc_rule_lhs_suffix_total_impl TA qs lr"
  using assms unfolding rfc_lhs_suffix_total_impl_def
  by (auto simp: list_all_iff)

lemma rfc_rule_lhs_suffix_total_implD:
  assumes total: "rfc_rule_lhs_suffix_total_impl TA qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<length lw]"
    and q: "q \<in> set qs"
  obtains m where "m \<in> set qs" and "rfc_word_reaches_impl TA q (drop i lw) m"
proof -
  from total words i q have "rfc_word_reaches_some_impl TA qs (drop i lw) q"
    unfolding rfc_rule_lhs_suffix_total_impl_def
    by (auto simp: list_all_iff)
  then show ?thesis
    by (rule rfc_word_reaches_some_implD) (fact that)
qed

lemma rfc_rule_lhs_suffix_total_impl_nonempty:
  assumes total: "rfc_rule_lhs_suffix_total_impl TA qs lr"
    and words: "rfc_rule_words lr = Some (lw, rw)"
  shows "lw \<noteq> []"
  using total words unfolding rfc_rule_lhs_suffix_total_impl_def
  by auto

lemma rfc_lhs_suffix_total_implD:
  assumes total: "rfc_lhs_suffix_total_impl TA qs R"
    and lr: "lr \<in> set R"
    and words: "rfc_rule_words lr = Some (lw, rw)"
    and i: "i \<in> set [1..<length lw]"
    and q: "q \<in> set qs"
  obtains m where "m \<in> set qs" and "rfc_word_reaches_impl TA q (drop i lw) m"
proof -
  have "rfc_rule_lhs_suffix_total_impl TA qs lr"
    by (rule rfc_lhs_suffix_total_impl_rule[OF total lr])
  then show ?thesis
    by (rule rfc_rule_lhs_suffix_total_implD[OF _ words i q]) (fact that)
qed

lemma rfc_lhs_suffix_total_impl_nonempty:
  assumes total: "rfc_lhs_suffix_total_impl TA qs R"
    and lr: "lr \<in> set R"
    and words: "rfc_rule_words lr = Some (lw, rw)"
  shows "lw \<noteq> []"
  using rfc_rule_lhs_suffix_total_impl_nonempty[
    OF rfc_lhs_suffix_total_impl_rule[OF total lr] words] .

definition
  rfc_word_overlap_step ::
    "('f,string)rules \<Rightarrow> 'f list \<Rightarrow> 'f list \<Rightarrow> bool"
where
  "rfc_word_overlap_step R sw tw \<equiv>
    \<exists>lr lw rw k rest.
      lr \<in> set R \<and>
      rfc_rule_words lr = Some (lw, rw) \<and>
      lw \<noteq> [] \<and>
      k < length sw \<and>
      ((drop k sw = lw @ rest \<and> tw = take k sw @ rw @ rest) \<or>
       (lw = drop k sw @ rest \<and> tw = take k sw @ rw))"

lemma rfc_word_overlap_step_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_automaton_closed_impl TAi qs R"
    and suffix_total: "rfc_lhs_suffix_total_impl TAi qs R"
    and step: "rfc_word_overlap_step R sw tw"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and source_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')))"
proof -
  from step obtain lr lw rw k rest where
    lr: "lr \<in> set R" and words: "rfc_rule_words lr = Some (lw, rw)"
    and lw_ne: "lw \<noteq> []"
    and k: "k < length sw"
    and cases: "(drop k sw = lw @ rest \<and> tw = take k sw @ rw @ rest) \<or>
      (lw = drop k sw @ rest \<and> tw = take k sw @ rw)"
    unfolding rfc_word_overlap_step_def by blast
  from source_acc[OF q_state] obtain qf where qf_fin: "qf \<in> ta_final (ta_of TAi)"
    and source: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
    by blast
  from k have sw_decomp: "sw = take k sw @ drop k sw"
    by simp
  from cases show ?thesis
  proof
    assume left: "drop k sw = lw @ rest \<and> tw = take k sw @ rw @ rest"
    then have drop: "drop k sw = lw @ rest" and tw: "tw = take k sw @ rw @ rest"
      by auto
    have source': "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q)
        (lift_term 0 (rfc_word_term ((take k sw @ lw) @ rest) ''x'')))"
      using source sw_decomp drop by (simp add: append_assoc)
    have split_source: "\<exists>m.
      m \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rest ''x''))) \<and>
      qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take k sw @ lw) ''x'')))"
      by (rule rfc_word_ta_res_append_ex[
          where xs = "take k sw @ lw" and ys = rest, OF source'])
    from split_source
    obtain m where rest_run: "m \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rest ''x'')))"
      and ctx_lhs: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take k sw @ lw) ''x'')))"
      by blast
    have m_state: "m \<in> ta_states (ta_of TAi)"
      using q_state rest_run by (rule rfc_word_ta_res_state)
    have split_ctx_lhs: "\<exists>p.
      p \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term lw ''x''))) \<and>
      qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
      by (rule rfc_word_ta_res_append_ex[
          where xs = "take k sw" and ys = lw, OF ctx_lhs])
    from split_ctx_lhs
    obtain p where lhs_run: "p \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term lw ''x'')))"
      and ctx_run: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
      by blast
    have p_state: "p \<in> ta_states (ta_of TAi)"
      using m_state lhs_run by (rule rfc_word_ta_res_state)
    have i_full: "length lw \<in> set [1..<Suc (length lw)]"
      using lw_ne by simp
    have i_full_le: "length lw \<le> length lw"
      by simp
    have rhs_run: "p \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term rw ''x'')))"
      by (rule rfc_rule_automaton_closed_impl_semantic[
          OF inv state_cover _ words i_full i_full_le m_state p_state lhs_run])
        (auto intro: rfc_automaton_closed_impl_rule[OF closed lr])
    have ctx_rhs: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m)
          (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
      by (rule rfc_word_ta_res_append[OF rhs_run ctx_run])
    have target: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q)
          (lift_term 0 (rfc_word_term (take k sw @ rw @ rest) ''x'')))"
      using rfc_word_ta_res_append[OF rest_run ctx_rhs] by simp
    with qf_fin tw show ?thesis by blast
  next
    assume right: "lw = drop k sw @ rest \<and> tw = take k sw @ rw"
    then have lw: "lw = drop k sw @ rest" and tw: "tw = take k sw @ rw"
      by auto
    let ?i = "length (drop k sw)"
    have i_pos: "0 < ?i"
      using k by simp
    show ?thesis
    proof (cases "rest = []")
      case True
      with lw have lw_eq: "lw = drop k sw"
        by simp
      have source': "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q)
          (lift_term 0 (rfc_word_term (take k sw @ lw) ''x'')))"
        using source sw_decomp lw_eq by simp
      from rfc_word_ta_res_appendE[OF source']
      obtain p where lhs_run: "p \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term lw ''x'')))"
        and ctx_run: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
        by blast
      have p_state: "p \<in> ta_states (ta_of TAi)"
        using q_state lhs_run by (rule rfc_word_ta_res_state)
      have i_full: "length lw \<in> set [1..<Suc (length lw)]"
        using lw_ne by simp
      have i_full_le: "length lw \<le> length lw"
        by simp
      have rhs_run: "p \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rw ''x'')))"
        by (rule rfc_rule_automaton_closed_impl_semantic[
            OF inv state_cover _ words i_full i_full_le q_state p_state lhs_run])
          (auto intro: rfc_automaton_closed_impl_rule[OF closed lr])
      have target: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
        by (rule rfc_word_ta_res_append[OF rhs_run ctx_run])
      with qf_fin tw show ?thesis by blast
    next
      case False
      have i_lt: "?i < length lw"
        using lw False by simp
      have i_mem: "?i \<in> set [1..<length lw]"
        using i_pos i_lt by simp
      have q_qs: "q \<in> set qs"
        using state_cover q_state by blast
      from rfc_lhs_suffix_total_implD[OF suffix_total lr words i_mem q_qs]
      obtain m where m_qs: "m \<in> set qs"
        and suffix_impl: "rfc_word_reaches_impl TAi q (drop ?i lw) m"
        by blast
      have suffix_run: "m \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (drop ?i lw) ''x'')))"
        by (rule rfc_word_reaches_impl_sound[OF inv suffix_impl])
      have i_mem': "?i \<in> set [1..<Suc (length lw)]"
        using i_pos i_lt by simp
      have i_le: "?i \<le> length lw"
        using i_lt by simp
      have take_i: "take ?i lw = drop k sw"
        using lw by simp
      have sw_eq: "sw = take k sw @ take ?i lw"
        using sw_decomp take_i by simp
      have source_acc': "\<And>q'. q' \<in> ta_states (ta_of TAi) \<Longrightarrow>
        \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q') (lift_term 0
            (rfc_word_term (take k sw @ take ?i lw) ''x'')))"
        using source_acc sw_eq by simp
      have target: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
        by (rule rfc_automaton_closed_impl_split_accept[
            OF inv state_cover closed lr words i_mem' i_le q_state suffix_run source_acc'])
      with tw show ?thesis by blast
    qed
  qed
qed

lemma rfc_matchbox_word_overlap_step_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TAi rel_info tails qs R"
    and step: "rfc_word_overlap_step R sw tw"
    and q_tail: "q \<in> set tails"
    and q_state: "q \<in> ta_states (ta_of TAi)"
    and source_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')))"
proof -
  from step obtain lr lw rw k rest where
    lr: "lr \<in> set R" and words: "rfc_rule_words lr = Some (lw, rw)"
    and lw_ne: "lw \<noteq> []"
    and k: "k < length sw"
    and cases: "(drop k sw = lw @ rest \<and> tw = take k sw @ rw @ rest) \<or>
      (lw = drop k sw @ rest \<and> tw = take k sw @ rw)"
    unfolding rfc_word_overlap_step_def by blast
  from source_acc obtain qf where qf_fin: "qf \<in> ta_final (ta_of TAi)"
    and source: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
    by blast
  from k have sw_decomp: "sw = take k sw @ drop k sw"
    by simp
  from cases show ?thesis
  proof
    assume left: "drop k sw = lw @ rest \<and> tw = take k sw @ rw @ rest"
    then have drop: "drop k sw = lw @ rest" and tw: "tw = take k sw @ rw @ rest"
      by auto
    have source': "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q)
        (lift_term 0 (rfc_word_term ((take k sw @ lw) @ rest) ''x'')))"
      using source sw_decomp drop by (simp add: append_assoc)
    from rfc_word_ta_res_append_ex[
        where xs = "take k sw @ lw" and ys = rest, OF source']
    obtain m where rest_run: "m \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term rest ''x'')))"
      and ctx_lhs: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (take k sw @ lw) ''x'')))"
      by blast
    have m_state: "m \<in> ta_states (ta_of TAi)"
      using q_state rest_run by (rule rfc_word_ta_res_state)
    from rfc_word_ta_res_append_ex[
        where xs = "take k sw" and ys = lw, OF ctx_lhs]
    obtain p where lhs_run: "p \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term lw ''x'')))"
      and ctx_run: "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
      by blast
    have p_state: "p \<in> ta_states (ta_of TAi)"
      using m_state lhs_run by (rule rfc_word_ta_res_state)
    have qf_state: "qf \<in> ta_states (ta_of TAi)"
      using qf_fin unfolding ta_states_def by auto
    have i_full: "length lw \<in> set [1..<Suc (length lw)]"
      using lw_ne by simp
    have i_full_le: "length lw \<le> length lw"
      by simp
    have closed_lr: "rfc_rule_matchbox_closed_impl TAi rel_info qs lr"
      by (rule rfc_matchbox_closed_impl_rule[OF closed lr])
    have suffix_empty_m: "m \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term (drop (length lw) lw) ''x'')))"
      by simp
    have lhs_run_full: "p \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m)
          (lift_term 0 (rfc_word_term (take (length lw) lw) ''x'')))"
      using lhs_run by simp
    from rfc_rule_matchbox_closed_impl_semantic_context[
        where lr = lr and lw = lw and rw = rw and i = "length lw"
          and q = m and m = m and p = p and qf = qf and pre = "take k sw",
        OF inv state_cover coh closed_lr words i_full i_full_le
          m_state p_state qf_state suffix_empty_m lhs_run_full ctx_run]
    obtain qf' where qf_rel: "(qf,qf') \<in> relation_of rel_info"
      and ctx_rhs: "qf' \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. m)
          (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
      by blast
    have qf'_fin: "qf' \<in> ta_final (ta_of TAi)"
      using state_coherentE2(1)[OF coh] qf_fin qf_rel by auto
    have target: "qf' \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q)
          (lift_term 0 (rfc_word_term (take k sw @ rw @ rest) ''x'')))"
      using rfc_word_ta_res_append[OF rest_run ctx_rhs] by simp
    with qf'_fin tw show ?thesis by blast
  next
    assume right: "lw = drop k sw @ rest \<and> tw = take k sw @ rw"
    then have lw: "lw = drop k sw @ rest" and tw: "tw = take k sw @ rw"
      by auto
    let ?i = "length (drop k sw)"
    have i_pos: "0 < ?i"
      using k by simp
    show ?thesis
    proof (cases "rest = []")
      case True
      with lw have lw_eq: "lw = drop k sw"
        by simp
      have source': "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q)
          (lift_term 0 (rfc_word_term (take k sw @ lw) ''x'')))"
        using source sw_decomp lw_eq by simp
      from rfc_word_ta_res_appendE[OF source']
      obtain p where lhs_run: "p \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term lw ''x'')))"
        and ctx_run: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
        by blast
      have p_state: "p \<in> ta_states (ta_of TAi)"
        using q_state lhs_run by (rule rfc_word_ta_res_state)
      have qf_state: "qf \<in> ta_states (ta_of TAi)"
        using qf_fin unfolding ta_states_def by auto
      have i_full: "length lw \<in> set [1..<Suc (length lw)]"
        using lw_ne by simp
      have i_full_le: "length lw \<le> length lw"
        by simp
      have suffix_empty: "q \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (drop (length lw) lw) ''x'')))"
        by simp
      have lhs_run_full: "p \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take (length lw) lw) ''x'')))"
        using lhs_run by simp
      have closed_lr: "rfc_rule_matchbox_closed_impl TAi rel_info qs lr"
        by (rule rfc_matchbox_closed_impl_rule[OF closed lr])
      from rfc_rule_matchbox_closed_impl_semantic_context[
          where lr = lr and lw = lw and rw = rw and i = "length lw"
            and q = q and m = q and p = p and qf = qf and pre = "take k sw",
          OF inv state_cover coh closed_lr words i_full i_full_le
            q_state p_state qf_state suffix_empty lhs_run_full ctx_run]
      obtain qf' where qf_rel: "(qf,qf') \<in> relation_of rel_info"
        and target: "qf' \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
        by blast
      have qf'_fin: "qf' \<in> ta_final (ta_of TAi)"
        using state_coherentE2(1)[OF coh] qf_fin qf_rel by auto
      with target tw show ?thesis by blast
    next
      case False
      have i_lt: "?i < length lw"
        using lw False by simp
      have i_mem: "?i \<in> set [1..<length lw]"
        using i_pos i_lt by simp
      have take_i: "take ?i lw = drop k sw"
        using lw by simp
      have source': "qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q)
          (lift_term 0 (rfc_word_term (take k sw @ take ?i lw) ''x'')))"
        using source sw_decomp take_i by simp
      from rfc_word_ta_res_appendE[OF source']
      obtain p where prefix_lhs: "p \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take ?i lw) ''x'')))"
        and prefix_context: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. p) (lift_term 0 (rfc_word_term (take k sw) ''x'')))"
        by blast
      have p_state: "p \<in> ta_states (ta_of TAi)"
        using q_state prefix_lhs by (rule rfc_word_ta_res_state)
      have qf_state: "qf \<in> ta_states (ta_of TAi)"
        using qf_fin unfolding ta_states_def by auto
      have ext_lr: "rfc_rule_matchbox_ext_right_impl TAi rel_info tails qs lr"
        by (rule rfc_matchbox_ext_right_impl_rule[OF ext_right lr])
      from rfc_rule_matchbox_ext_right_impl_semantic_context[
          where lr = lr and lw = lw and rw = rw and i = ?i
            and q = q and p = p and qf = qf and pre = "take k sw",
          OF inv state_cover coh ext_lr words i_mem q_tail q_state p_state qf_state
            prefix_lhs prefix_context]
      obtain qf' where qf_rel: "(qf,qf') \<in> relation_of rel_info"
        and target: "qf' \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q)
            (lift_term 0 (rfc_word_term (take k sw @ rw) ''x'')))"
        by blast
      have qf'_fin: "qf' \<in> ta_final (ta_of TAi)"
        using state_coherentE2(1)[OF coh] qf_fin qf_rel by auto
      with target tw show ?thesis by blast
    qed
  qed
qed

lemma rfc_word_term_subst_append:
  "rfc_word_term (xs @ ys) x \<cdot> \<sigma> =
    rfc_word_term xs x \<cdot> (\<lambda>_. rfc_word_term ys x \<cdot> \<sigma>)"
  by (induct xs) auto

lemma rfc_word_term_subst_append_any_tail:
  "rfc_word_term xs x \<cdot> (\<lambda>_. rfc_word_term ys y \<cdot> \<sigma>) =
    rfc_word_term (xs @ ys) y \<cdot> \<sigma>"
  by (induct xs) auto

lemma map_vars_lift_rfc_word_term_tail_irrel:
  "map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w x)) =
    map_vars_term (\<lambda>_. q) (lift_term h (rfc_word_term w y))"
  by (induct w) auto

lemma rfc_word_term_subst_word_tail:
  "rfc_word_term xs x \<cdot> (\<lambda>_. rfc_word_term ys z) = rfc_word_term (xs @ ys) z"
  by (induct xs) auto

lemma subst_of_single[simp]:
  "subst_of [(x,t)] = subst x t"
  by (rule ext) (simp add: subst_compose_def)

lemma x_var_neq_y_var[simp]:
  "x_var x \<noteq> y_var y"
  by simp

lemma subst_x_var_at_y_var[simp]:
  "subst (x_var x) t (y_var y) = Var (y_var y)"
  by (simp add: subst_def)

lemma subst_y_var_at_x_var[simp]:
  "subst (y_var y) t (x_var x) = Var (x_var x)"
  by (simp add: subst_def)

lemma mgu_rfc_word_term_left_prefix:
  assumes xy: "x \<noteq> y"
  shows "mgu (rfc_word_term v x) (rfc_word_term (v @ rest) y) =
    Some (subst x (rfc_word_term rest y))"
  using assms
proof (induct v)
  case Nil
  then show ?case
    unfolding mgu_def
    by (cases rest) (simp_all add: subst_list_def)
next
  case (Cons f v)
  then show ?case
    unfolding mgu_def
    by (simp add: subst_list_def decompose_def zip_option.simps
        rfc_word_term_subst_append_any_tail)
qed

lemma mgu_rfc_word_term_same_word:
  assumes xy: "x \<noteq> y"
  shows "mgu (rfc_word_term w x) (rfc_word_term w y) = Some (subst x (Var y))"
  using assms
proof (induct w)
  case Nil
  then show ?case
    unfolding mgu_def by (simp add: subst_list_def)
next
  case (Cons f w)
  then show ?case
    unfolding mgu_def
    by (simp add: subst_list_def decompose_def zip_option.simps)
qed

lemma mgu_rfc_word_term_right_proper_prefix:
  assumes xy: "x \<noteq> y"
    and rest: "rest \<noteq> []"
  shows "mgu (rfc_word_term (w @ rest) x) (rfc_word_term w y) =
    Some (subst y (rfc_word_term rest x))"
  using assms
proof (induct w)
  case Nil
  then show ?case
    unfolding mgu_def
    by (cases rest) (simp_all add: subst_list_def)
next
  case (Cons f w)
  then show ?case
    unfolding mgu_def
    by (simp add: subst_list_def decompose_def zip_option.simps
        rfc_word_term_subst_append_any_tail)
qed

lemma mgu_vd_string_rfc_word_left_prefix:
  "mgu_vd_string (rfc_word_term v x) (rfc_word_term (v @ rest) y) =
    Some (subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> x_var,
      subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> y_var)"
proof -
  have m: "mgu (map_vars_term x_var (rfc_word_term v x))
      (map_vars_term y_var (rfc_word_term (v @ rest) y)) =
    Some (subst (x_var x) (rfc_word_term rest (y_var y)))"
    apply (simp only: map_vars_term_rfc_word_term rfc_word_term_subst_word_tail)
    apply (rule mgu_rfc_word_term_left_prefix)
    apply simp
    done
  have m0: "mgu (rfc_word_term v (x_var x))
      (rfc_word_term (v @ rest) (y_var y)) =
    Some (subst (x_var x) (rfc_word_term rest (y_var y)))"
    using m by simp
  show ?thesis
    unfolding mgu_vd_string_code mgu_var_disjoint_generic_def
    by (simp add: m0)
qed

lemma mgu_vd_string_rfc_word_same_word:
  "mgu_vd_string (rfc_word_term w x) (rfc_word_term w y) =
    Some (subst (x_var x) (Var (y_var y)) \<circ> x_var,
      subst (x_var x) (Var (y_var y)) \<circ> y_var)"
  unfolding mgu_vd_string_code mgu_var_disjoint_generic_def
  by (simp add: mgu_rfc_word_term_same_word)

lemma mgu_vd_string_rfc_word_right_proper_prefix:
  assumes rest: "rest \<noteq> []"
  shows "mgu_vd_string (rfc_word_term (w @ rest) x) (rfc_word_term w y) =
    Some (subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> x_var,
      subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> y_var)"
proof -
  have m: "mgu (map_vars_term x_var (rfc_word_term (w @ rest) x))
      (map_vars_term y_var (rfc_word_term w y)) =
    Some (subst (y_var y) (rfc_word_term rest (x_var x)))"
    apply (simp only: map_vars_term_rfc_word_term rfc_word_term_subst_word_tail)
    apply (rule mgu_rfc_word_term_right_proper_prefix)
     apply simp
    apply (rule rest)
    done
  have m0: "mgu (rfc_word_term (w @ rest) (x_var x))
      (rfc_word_term w (y_var y)) =
    Some (subst (y_var y) (rfc_word_term rest (x_var x)))"
    using m by simp
  show ?thesis
    unfolding mgu_vd_string_code mgu_var_disjoint_generic_def
    by (simp add: m0)
qed

lemma rfc_word_term_subst_xvar_left_prefix[simp]:
  "rfc_word_term w x \<cdot> (subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> x_var) =
    rfc_word_term (w @ rest) (y_var y)"
  by (induct w) auto

lemma rfc_word_term_subst_yvar_left_prefix[simp]:
  "rfc_word_term w y \<cdot> (subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> y_var) =
    rfc_word_term w (y_var y)"
  by (induct w) (auto simp: subst_def)

lemma rfc_word_term_subst_xvar_right_proper_prefix[simp]:
  "rfc_word_term w x \<cdot> (subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> x_var) =
    rfc_word_term w (x_var x)"
  by (induct w) (auto simp: subst_def)

lemma rfc_word_term_subst_yvar_right_proper_prefix[simp]:
  "rfc_word_term w y \<cdot> (subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> y_var) =
    rfc_word_term (w @ rest) (x_var x)"
  by (induct w) auto

lemma mgu_vd_string_rfc_word_prefix_cases:
  assumes mgu: "mgu_vd_string (rfc_word_term sw x) (rfc_word_term lw y) =
    Some (\<mu>1,\<mu>2)"
  shows
    "(\<exists>rest. lw = sw @ rest \<and>
        \<mu>1 = subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> x_var \<and>
        \<mu>2 = subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> y_var) \<or>
     (\<exists>rest. rest \<noteq> [] \<and> sw = lw @ rest \<and>
        \<mu>1 = subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> x_var \<and>
        \<mu>2 = subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> y_var)"
proof -
  from mgu_vd_string_sound[OF mgu]
  have eq: "rfc_word_term sw x \<cdot> \<mu>1 = rfc_word_term lw y \<cdot> \<mu>2" .
  from rfc_word_term_subst_eq_prefix_cases[OF eq] show ?thesis
  proof
    assume "\<exists>rest. lw = sw @ rest \<and> \<mu>1 x = rfc_word_term rest y \<cdot> \<mu>2"
    then obtain rest where lw: "lw = sw @ rest" by auto
    have exact: "mgu_vd_string (rfc_word_term sw x) (rfc_word_term lw y) =
      Some (subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> x_var,
        subst (x_var x) (rfc_word_term rest (y_var y)) \<circ> y_var)"
      unfolding lw by (rule mgu_vd_string_rfc_word_left_prefix)
    from mgu exact lw show ?thesis
      by (intro disjI1 exI[of _ rest]) auto
  next
    assume "\<exists>rest. sw = lw @ rest \<and> \<mu>2 y = rfc_word_term rest x \<cdot> \<mu>1"
    then obtain rest where sw: "sw = lw @ rest" by auto
    show ?thesis
    proof (cases "rest = []")
      case True
      with sw have lw: "lw = sw @ []" by simp
      have exact: "mgu_vd_string (rfc_word_term sw x) (rfc_word_term lw y) =
        Some (subst (x_var x) (rfc_word_term [] (y_var y)) \<circ> x_var,
          subst (x_var x) (rfc_word_term [] (y_var y)) \<circ> y_var)"
        unfolding lw by (rule mgu_vd_string_rfc_word_left_prefix)
      from mgu exact lw show ?thesis by auto
    next
      case False
      have exact: "mgu_vd_string (rfc_word_term sw x) (rfc_word_term lw y) =
        Some (subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> x_var,
          subst (y_var y) (rfc_word_term rest (x_var x)) \<circ> y_var)"
        unfolding sw by (rule mgu_vd_string_rfc_word_right_proper_prefix[OF False])
      from mgu exact sw False show ?thesis by auto
    qed
  qed
qed

lemma ta_res_append_word_context:
  fixes TA :: "('q,'f \<times> nat)ta"
  assumes suffix: "m \<in> ta_res TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term ys ''x'')))"
    and prefix: "qf \<in> ta_res TA
      (map_vars_term (\<lambda>_. m) (lift_term 0 (rfc_word_term xs ''x'')))"
  shows "qf \<in> ta_res TA
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term (xs @ ys) ''x'')))"
  by (rule rfc_word_ta_res_append[OF suffix prefix])

lemma rfc_word_term_replace_subst_prefix:
  assumes i: "i \<le> length w"
  shows "replace_at (rfc_word_term w x \<cdot> \<sigma>) (replicate i 0) t =
    rfc_word_term (take i w) x \<cdot> (\<lambda>_. t)"
  using assms
proof (induct w arbitrary: i)
  case Nil
  then show ?case by (cases i) auto
next
  case (Cons f w)
  then show ?case by (cases i) auto
qed

lemma rfc_narrows_impl_rfc_word_overlap:
  assumes closed: "rfc_automaton_closed_impl TA qs R"
    and suffix_total: "rfc_lhs_suffix_total_impl TA qs R"
    and step: "u \<in> set (rfc_narrows_impl R (rfc_word_term sw x))"
  shows "\<exists>tw y. u = rfc_word_term tw y \<and> rfc_word_overlap_step R sw tw"
proof -
  from step obtain p l r \<mu>1 \<mu>2 where
    p: "p \<in> poss (rfc_word_term sw x)"
    and is_fun: "is_Fun (rfc_word_term sw x |_ p)"
    and lr: "(l,r) \<in> set R"
    and mgu: "mgu_vd_string (rfc_word_term sw x |_ p) l = Some (\<mu>1,\<mu>2)"
    and u_def: "u = replace_at (rfc_word_term sw x \<cdot> \<mu>1) p (r \<cdot> \<mu>2)"
    unfolding rfc_narrows_impl by auto
  from rfc_word_term_poss_fun_replicate[OF p is_fun]
  obtain k where k: "k < length sw" and p_rep: "p = replicate k 0"
    by blast
  have k_le: "k \<le> length sw" using k by simp
  have subt: "rfc_word_term sw x |_ p = rfc_word_term (drop k sw) x"
    unfolding p_rep by (rule rfc_word_term_subt_at_replicate[OF k_le])
  from rfc_automaton_closed_impl_rule_words[OF closed lr]
  obtain lw rw where words: "rfc_rule_words (l,r) = Some (lw,rw)"
    by blast
  from rfc_lhs_suffix_total_impl_nonempty[OF suffix_total lr words]
  have lw_ne: "lw \<noteq> []" .
  from rfc_rule_words_sound[OF words]
  obtain vx where l_def: "l = rfc_word_term lw vx" and r_def: "r = rfc_word_term rw vx"
    by auto
  from mgu[unfolded subt l_def]
  have pcases: "(\<exists>rest. lw = drop k sw @ rest \<and>
        \<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var \<and>
        \<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var) \<or>
     (\<exists>rest. rest \<noteq> [] \<and> drop k sw = lw @ rest \<and>
        \<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var \<and>
        \<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var)"
    by (rule mgu_vd_string_rfc_word_prefix_cases)
  from pcases show ?thesis
  proof
    assume "\<exists>rest. lw = drop k sw @ rest \<and>
        \<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var \<and>
        \<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var"
    then obtain rest where lw: "lw = drop k sw @ rest"
      and mu1: "\<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var"
      and mu2: "\<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var"
      by blast
    let ?tw = "take k sw @ rw"
    have r_mu: "r \<cdot> \<mu>2 = rfc_word_term rw (y_var vx)"
      unfolding r_def mu2 by (induct rw) auto
    have src_mu: "rfc_word_term sw x \<cdot> \<mu>1 = rfc_word_term (sw @ rest) (y_var vx)"
      by (simp only: mu1 rfc_word_term_subst_xvar_left_prefix)
    have u_word: "u = rfc_word_term ?tw (y_var vx)"
    proof -
      have "u = replace_at (rfc_word_term (sw @ rest) (y_var vx)) (replicate k 0)
          (rfc_word_term rw (y_var vx))"
        unfolding u_def p_rep r_mu using src_mu by simp
      also have "\<dots> = rfc_word_term (take k (sw @ rest) @ rw) (y_var vx)"
        by (rule rfc_word_term_replace_at_replicate) (use k_le in simp)
      also have "\<dots> = rfc_word_term ?tw (y_var vx)"
        using k_le by simp
      finally show ?thesis .
    qed
    have ov: "rfc_word_overlap_step R sw ?tw"
    proof -
      have alt: "(drop k sw = lw @ rest \<and> ?tw = take k sw @ rw @ rest) \<or>
        (lw = drop k sw @ rest \<and> ?tw = take k sw @ rw)"
        using lw by simp
      show ?thesis
        unfolding rfc_word_overlap_step_def
      proof (intro exI conjI)
        show "(l, r) \<in> set R" by (rule lr)
      next
        show "rfc_rule_words (l, r) = Some (lw, rw)" by (rule words)
      next
        show "lw \<noteq> []" by (rule lw_ne)
      next
        show "k < length sw" by (rule k)
      next
        show "(drop k sw = lw @ rest \<and> take k sw @ rw = take k sw @ rw @ rest) \<or>
          lw = drop k sw @ rest \<and> take k sw @ rw = take k sw @ rw"
          using alt by simp
      qed
    qed
    from u_word ov show ?thesis by blast
  next
    assume "\<exists>rest. rest \<noteq> [] \<and> drop k sw = lw @ rest \<and>
        \<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var \<and>
        \<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var"
    then obtain rest where rest_ne: "rest \<noteq> []" and drop: "drop k sw = lw @ rest"
      and mu1: "\<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var"
      and mu2: "\<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var"
      by blast
    let ?tw = "take k sw @ rw @ rest"
    have r_mu: "r \<cdot> \<mu>2 = rfc_word_term (rw @ rest) (x_var x)"
      unfolding r_def mu2 by (induct rw) auto
    have src_mu: "rfc_word_term sw x \<cdot> \<mu>1 = rfc_word_term sw (x_var x)"
      by (simp only: mu1 rfc_word_term_subst_xvar_right_proper_prefix)
    have u_word: "u = rfc_word_term ?tw (x_var x)"
    proof -
      have u0: "u = replace_at (rfc_word_term sw (x_var x)) (replicate k 0)
          (rfc_word_term (rw @ rest) (x_var x))"
        unfolding u_def p_rep r_mu using src_mu by simp
      have rep: "replace_at (rfc_word_term sw (x_var x)) (replicate k 0)
          (rfc_word_term (rw @ rest) (x_var x)) =
        rfc_word_term (take k sw @ (rw @ rest)) (x_var x)"
        by (rule rfc_word_term_replace_at_replicate[OF k_le])
      from u0 rep show ?thesis by (simp add: append_assoc)
    qed
    have ov: "rfc_word_overlap_step R sw ?tw"
    proof -
      have alt: "(drop k sw = lw @ rest \<and> ?tw = take k sw @ rw @ rest) \<or>
        (lw = drop k sw @ rest \<and> ?tw = take k sw @ rw)"
        using drop by simp
      show ?thesis
        unfolding rfc_word_overlap_step_def
      proof (intro exI conjI)
        show "(l, r) \<in> set R" by (rule lr)
      next
        show "rfc_rule_words (l, r) = Some (lw, rw)" by (rule words)
      next
        show "lw \<noteq> []" by (rule lw_ne)
      next
        show "k < length sw" by (rule k)
      next
        show "(drop k sw = lw @ rest \<and> take k sw @ rw @ rest = take k sw @ rw @ rest) \<or>
          lw = drop k sw @ rest \<and> take k sw @ rw @ rest = take k sw @ rw"
          using alt by simp
      qed
    qed
    from u_word ov show ?thesis by blast
  qed
qed

lemma rfc_matchbox_narrows_impl_rfc_word_overlap:
  assumes closed: "rfc_matchbox_closed_impl TA rel qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TA rel tails qs R"
    and step: "u \<in> set (rfc_narrows_impl R (rfc_word_term sw x))"
  shows "\<exists>tw y. u = rfc_word_term tw y \<and> rfc_word_overlap_step R sw tw"
proof -
  from step obtain p l r \<mu>1 \<mu>2 where
    p: "p \<in> poss (rfc_word_term sw x)"
    and is_fun: "is_Fun (rfc_word_term sw x |_ p)"
    and lr: "(l,r) \<in> set R"
    and mgu: "mgu_vd_string (rfc_word_term sw x |_ p) l = Some (\<mu>1,\<mu>2)"
    and u_def: "u = replace_at (rfc_word_term sw x \<cdot> \<mu>1) p (r \<cdot> \<mu>2)"
    unfolding rfc_narrows_impl by auto
  from rfc_word_term_poss_fun_replicate[OF p is_fun]
  obtain k where k: "k < length sw" and p_rep: "p = replicate k 0"
    by blast
  have k_le: "k \<le> length sw" using k by simp
  have subt: "rfc_word_term sw x |_ p = rfc_word_term (drop k sw) x"
    unfolding p_rep by (rule rfc_word_term_subt_at_replicate[OF k_le])
  from rfc_matchbox_closed_impl_rule_words[OF closed lr]
  obtain lw rw where words: "rfc_rule_words (l,r) = Some (lw,rw)"
    by blast
  from rfc_matchbox_ext_right_impl_rule_words[OF ext_right lr] words
  have lw_ne: "lw \<noteq> []" by auto
  from rfc_rule_words_sound[OF words]
  obtain vx where l_def: "l = rfc_word_term lw vx" and r_def: "r = rfc_word_term rw vx"
    by auto
  from mgu[unfolded subt l_def]
  have pcases: "(\<exists>rest. lw = drop k sw @ rest \<and>
        \<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var \<and>
        \<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var) \<or>
     (\<exists>rest. rest \<noteq> [] \<and> drop k sw = lw @ rest \<and>
        \<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var \<and>
        \<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var)"
    by (rule mgu_vd_string_rfc_word_prefix_cases)
  from pcases show ?thesis
  proof
    assume "\<exists>rest. lw = drop k sw @ rest \<and>
        \<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var \<and>
        \<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var"
    then obtain rest where lw: "lw = drop k sw @ rest"
      and mu1: "\<mu>1 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> x_var"
      and mu2: "\<mu>2 = subst (x_var x) (rfc_word_term rest (y_var vx)) \<circ> y_var"
      by blast
    let ?tw = "take k sw @ rw"
    have r_mu: "r \<cdot> \<mu>2 = rfc_word_term rw (y_var vx)"
      unfolding r_def mu2 by (induct rw) auto
    have src_mu: "rfc_word_term sw x \<cdot> \<mu>1 = rfc_word_term (sw @ rest) (y_var vx)"
      by (simp only: mu1 rfc_word_term_subst_xvar_left_prefix)
    have u_word: "u = rfc_word_term ?tw (y_var vx)"
    proof -
      have "u = replace_at (rfc_word_term (sw @ rest) (y_var vx)) (replicate k 0)
          (rfc_word_term rw (y_var vx))"
        unfolding u_def p_rep r_mu using src_mu by simp
      also have "\<dots> = rfc_word_term (take k (sw @ rest) @ rw) (y_var vx)"
        by (rule rfc_word_term_replace_at_replicate) (use k_le in simp)
      also have "\<dots> = rfc_word_term ?tw (y_var vx)"
        using k_le by simp
      finally show ?thesis .
    qed
    have ov: "rfc_word_overlap_step R sw ?tw"
    proof -
      have alt: "(drop k sw = lw @ rest \<and> ?tw = take k sw @ rw @ rest) \<or>
        (lw = drop k sw @ rest \<and> ?tw = take k sw @ rw)"
        using lw by simp
      show ?thesis
        unfolding rfc_word_overlap_step_def
      proof (intro exI conjI)
        show "(l, r) \<in> set R" by (rule lr)
      next
        show "rfc_rule_words (l, r) = Some (lw, rw)" by (rule words)
      next
        show "lw \<noteq> []" by (rule lw_ne)
      next
        show "k < length sw" by (rule k)
      next
        show "(drop k sw = lw @ rest \<and> take k sw @ rw = take k sw @ rw @ rest) \<or>
          lw = drop k sw @ rest \<and> take k sw @ rw = take k sw @ rw"
          using alt by simp
      qed
    qed
    from u_word ov show ?thesis by blast
  next
    assume "\<exists>rest. rest \<noteq> [] \<and> drop k sw = lw @ rest \<and>
        \<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var \<and>
        \<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var"
    then obtain rest where rest_ne: "rest \<noteq> []" and drop: "drop k sw = lw @ rest"
      and mu1: "\<mu>1 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> x_var"
      and mu2: "\<mu>2 = subst (y_var vx) (rfc_word_term rest (x_var x)) \<circ> y_var"
      by blast
    let ?tw = "take k sw @ rw @ rest"
    have r_mu: "r \<cdot> \<mu>2 = rfc_word_term (rw @ rest) (x_var x)"
      unfolding r_def mu2 by (induct rw) auto
    have src_mu: "rfc_word_term sw x \<cdot> \<mu>1 = rfc_word_term sw (x_var x)"
      by (simp only: mu1 rfc_word_term_subst_xvar_right_proper_prefix)
    have u_word: "u = rfc_word_term ?tw (x_var x)"
    proof -
      have u0: "u = replace_at (rfc_word_term sw (x_var x)) (replicate k 0)
          (rfc_word_term (rw @ rest) (x_var x))"
        unfolding u_def p_rep r_mu using src_mu by simp
      have rep: "replace_at (rfc_word_term sw (x_var x)) (replicate k 0)
          (rfc_word_term (rw @ rest) (x_var x)) =
        rfc_word_term (take k sw @ (rw @ rest)) (x_var x)"
        by (rule rfc_word_term_replace_at_replicate[OF k_le])
      from u0 rep show ?thesis by (simp add: append_assoc)
    qed
    have ov: "rfc_word_overlap_step R sw ?tw"
    proof -
      have alt: "(drop k sw = lw @ rest \<and> ?tw = take k sw @ rw @ rest) \<or>
        (lw = drop k sw @ rest \<and> ?tw = take k sw @ rw)"
        using drop by simp
      show ?thesis
        unfolding rfc_word_overlap_step_def
      proof (intro exI conjI)
        show "(l, r) \<in> set R" by (rule lr)
      next
        show "rfc_rule_words (l, r) = Some (lw, rw)" by (rule words)
      next
        show "lw \<noteq> []" by (rule lw_ne)
      next
        show "k < length sw" by (rule k)
      next
        show "(drop k sw = lw @ rest \<and> take k sw @ rw @ rest = take k sw @ rw @ rest) \<or>
          lw = drop k sw @ rest \<and> take k sw @ rw @ rest = take k sw @ rw"
          using alt by simp
      qed
    qed
    from u_word ov show ?thesis by blast
  qed
qed

lemma rfc_narrow_word_step_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_automaton_closed_impl TAi qs R"
    and suffix_total: "rfc_lhs_suffix_total_impl TAi qs R"
    and source_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
    and step: "(rfc_word_term sw x,u) \<in> rfc_narrow_step R"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 u))"
proof -
  from step have u_step: "u \<in> set (rfc_narrows_impl R (rfc_word_term sw x))"
    unfolding rfc_narrow_step_def by auto
  from rfc_narrows_impl_rfc_word_overlap[OF closed suffix_total u_step]
  obtain tw y where u: "u = rfc_word_term tw y" and ov: "rfc_word_overlap_step R sw tw"
    by blast
  from rfc_word_overlap_step_accepted[
      OF inv state_cover closed suffix_total ov q_state source_acc]
  obtain qf where qf: "qf \<in> ta_final (ta_of TAi)"
    and acc: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')))"
    by blast
  have tail: "map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')) =
    map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw y))"
    by (rule map_vars_lift_rfc_word_term_tail_irrel)
  with qf acc u show ?thesis by auto
qed

lemma rfc_matchbox_narrow_word_step_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TAi rel_info tails qs R"
    and source_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term sw ''x'')))"
    and step: "(rfc_word_term sw x,u) \<in> rfc_narrow_step R"
    and q_tail: "q \<in> set tails"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 u))"
proof -
  from step have u_step: "u \<in> set (rfc_narrows_impl R (rfc_word_term sw x))"
    unfolding rfc_narrow_step_def by auto
  from rfc_matchbox_narrows_impl_rfc_word_overlap[OF closed ext_right u_step]
  obtain tw y where u: "u = rfc_word_term tw y" and ov: "rfc_word_overlap_step R sw tw"
    by blast
  from rfc_matchbox_word_overlap_step_accepted[
      OF inv state_cover coh closed ext_right ov q_tail q_state source_acc]
  obtain qf where qf: "qf \<in> ta_final (ta_of TAi)"
    and acc: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')))"
    by blast
  have tail: "map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw ''x'')) =
    map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term tw y))"
    by (rule map_vars_lift_rfc_word_term_tail_irrel)
  with qf acc u show ?thesis by auto
qed

lemma rfc_automaton_closed_forward_closure_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi rel rell"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_automaton_closed_impl TAi qs R"
    and suffix_total: "rfc_lhs_suffix_total_impl TAi qs R"
    and covers: "rfc_initial_covers R I"
    and initial_acc: "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    and t: "t \<in> rfc_forward_closure R"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from t obtain s where s_rhs: "s \<in> rhss (set R)"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    unfolding rfc_forward_closure_def by auto
  from rfc_automaton_closed_impl_rhss_word[OF closed s_rhs]
  obtain sw sx where s_word: "s = rfc_word_term sw sx"
    by blast
  have s_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 s))"
  proof -
    fix q
    assume q: "q \<in> ta_states (ta_of TAi)"
    from rfc_initial_covers[OF covers] s_rhs have s_I: "s \<in> set I" by auto
    from initial_acc[OF s_I q] show "\<exists>qf\<in>ta_final (ta_of TAi).
      qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 s))" .
  qed
  have "\<exists>w x. t = rfc_word_term w x \<and>
    (\<forall>q\<in>ta_states (ta_of TAi).
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
    using steps s_word s_acc
  proof (induct arbitrary: sw sx)
    case base
    then show ?case by blast
  next
    case (step y z)
    then obtain yw yx where y_word: "y = rfc_word_term yw yx"
      and y_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
        \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
      by blast
    have y_acc_word: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
        \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x'')))"
    proof -
      fix q
      assume q: "q \<in> ta_states (ta_of TAi)"
      from y_acc[OF q] obtain qf where qf: "qf \<in> ta_final (ta_of TAi)"
        and acc: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
        by blast
      have tail: "map_vars_term (\<lambda>_. q) (lift_term 0 y) =
        map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x''))"
        unfolding y_word by (rule map_vars_lift_rfc_word_term_tail_irrel)
      with qf acc show "\<exists>qf\<in>ta_final (ta_of TAi).
        qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x'')))"
        by auto
    qed
    from step.hyps(2) y_word have z_step: "(rfc_word_term yw yx,z) \<in> rfc_narrow_step R"
      by simp
    from rfc_narrows_impl_rfc_word_overlap[OF closed suffix_total,
        of z yw yx] z_step
    obtain zw zx where z_word: "z = rfc_word_term zw zx"
      unfolding rfc_narrow_step_def by auto
    have z_acc: "\<And>q. q \<in> ta_states (ta_of TAi) \<Longrightarrow>
        \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 z))"
      by (rule rfc_narrow_word_step_accepted[
          OF inv state_cover closed suffix_total y_acc_word z_step])
    from z_word z_acc show ?case by blast
  qed
  then show ?thesis using q_state by blast
qed

lemma rfc_matchbox_closed_forward_closure_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TAi rel_info Q qs R"
    and covers: "rfc_initial_covers R I"
    and initial_acc: "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> set Q \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    and t: "t \<in> rfc_forward_closure R"
    and q: "q \<in> set Q"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from t obtain s where s_rhs: "s \<in> rhss (set R)"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    unfolding rfc_forward_closure_def by auto
  from rfc_matchbox_closed_impl_rhss_word[OF closed s_rhs]
  obtain sw sx where s_word: "s = rfc_word_term sw sx"
    by blast
  have s_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 s))"
  proof -
    from rfc_initial_covers[OF covers] s_rhs have s_I: "s \<in> set I" by auto
    from initial_acc[OF s_I q] show "\<exists>qf\<in>ta_final (ta_of TAi).
      qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 s))" .
  qed
  have "\<exists>w x. t = rfc_word_term w x \<and>
    (\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
    using steps s_word s_acc
  proof (induct arbitrary: sw sx)
    case base
    then show ?case by blast
  next
    case (step y z)
    then obtain yw yx where y_word: "y = rfc_word_term yw yx"
      and y_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
      by blast
    have y_acc_word: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x'')))"
    proof -
      from y_acc obtain qf where qf: "qf \<in> ta_final (ta_of TAi)"
        and acc: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
        by blast
      have tail: "map_vars_term (\<lambda>_. q) (lift_term 0 y) =
        map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x''))"
        unfolding y_word by (rule map_vars_lift_rfc_word_term_tail_irrel)
      with qf acc show "\<exists>qf\<in>ta_final (ta_of TAi).
        qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x'')))"
        by auto
    qed
    from step.hyps(2) y_word have z_step: "(rfc_word_term yw yx,z) \<in> rfc_narrow_step R"
      by simp
    from rfc_matchbox_narrows_impl_rfc_word_overlap[OF closed ext_right,
        of z yw yx] z_step
    obtain zw zx where z_word: "z = rfc_word_term zw zx"
      unfolding rfc_narrow_step_def by auto
    have z_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 z))"
      by (rule rfc_matchbox_narrow_word_step_accepted[
          OF inv state_cover coh closed ext_right y_acc_word z_step q q_state])
    from z_word z_acc show ?case by blast
  qed
  then show ?thesis by blast
qed

lemma rfc_native_matchbox_closed_forward_closure_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_native_matchbox_closed_impl
      TAi Id_Relation qs R"
    and ext_right: "rfc_native_matchbox_ext_right_impl
      TAi Id_Relation qs R"
    and wf: "wf_trs (set R)"
    and covers: "rfc_initial_covers R I"
    and initial_acc: "\<And>t q. t \<in> set I \<Longrightarrow> q \<in> set Q \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    and t: "t \<in> rfc_forward_closure R"
    and q: "q \<in> set Q"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  have old_closed: "rfc_matchbox_closed_impl
      TAi Id_Relation qs R"
    by (rule rfc_native_matchbox_closed_Id_imp[
      OF inv state_cover closed wf])
  have old_ext: "rfc_matchbox_ext_right_impl
      TAi Id_Relation Q qs R"
    by (rule rfc_native_matchbox_ext_right_Id_imp[
      OF inv state_cover ext_right])
  have coh: "state_coherent (ta_of TAi) Id"
    by (rule state_coherent_Id)
  have inv': "ta_inv TAi (rel_checker Id_Relation)
      (relation_of Id_Relation)"
    using inv by simp
  have coh': "state_coherent (ta_of TAi) (relation_of Id_Relation)"
    using coh by simp
  show ?thesis
    by (rule rfc_matchbox_closed_forward_closure_accepted[
      OF inv' state_cover coh' old_closed old_ext
        covers initial_acc t q q_state])
qed

lemma rfc_matchbox_narrow_steps_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TAi rel_info tails qs R"
    and s_word: "s = rfc_word_term sw sx"
    and source_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 s))"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    and q_tail: "q \<in> set tails"
    and q_state: "q \<in> ta_states (ta_of TAi)"
  shows "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
    (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  have "\<exists>w x. t = rfc_word_term w x \<and>
    (\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
    using steps s_word source_acc
  proof (induct arbitrary: sw sx)
    case base
    then show ?case by blast
  next
    case (step y z)
    then obtain yw yx where y_word: "y = rfc_word_term yw yx"
      and y_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
        (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
      by blast
    have y_acc_word: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x'')))"
    proof -
      from y_acc obtain qf where qf: "qf \<in> ta_final (ta_of TAi)"
        and acc: "qf \<in> ta_res (ta_of TAi)
          (map_vars_term (\<lambda>_. q) (lift_term 0 y))"
        by blast
      have tail: "map_vars_term (\<lambda>_. q) (lift_term 0 y) =
        map_vars_term (\<lambda>_. q) (lift_term 0 (rfc_word_term yw ''x''))"
        unfolding y_word by (rule map_vars_lift_rfc_word_term_tail_irrel)
      with qf acc show ?thesis by auto
    qed
    from step.hyps(2) y_word
    have z_step: "(rfc_word_term yw yx,z) \<in> rfc_narrow_step R"
      by simp
    from rfc_matchbox_narrows_impl_rfc_word_overlap[OF closed ext_right,
        of z yw yx] z_step
    obtain zw zx where z_word: "z = rfc_word_term zw zx"
      unfolding rfc_narrow_step_def by auto
    have z_acc: "\<exists>qf\<in>ta_final (ta_of TAi). qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 z))"
      by (rule rfc_matchbox_narrow_word_step_accepted[
          OF inv state_cover coh closed ext_right y_acc_word z_step q_tail q_state])
    from z_word z_acc show ?case by blast
  qed
  then show ?thesis by blast
qed

lemma rfc_matchbox_paired_forward_closure_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker rel_info) (relation_of rel_info)"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and coh: "state_coherent (ta_of TAi) (relation_of rel_info)"
    and closed: "rfc_matchbox_closed_impl TAi rel_info qs R"
    and ext_right: "rfc_matchbox_ext_right_impl TAi rel_info tails qs R"
    and covers: "rfc_initial_covers R I"
    and initial_acc: "rfc_initial_paired_accepted_impl TYPE('f) TAi tails I"
    and tails_final: "set tails \<subseteq> ta_final (ta_of TAi)"
    and t: "t \<in> rfc_forward_closure R"
  shows "\<exists>q\<in>set tails. \<exists>qf\<in>ta_final (ta_of TAi).
    qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  from t obtain s where s_rhs: "s \<in> rhss (set R)"
    and steps: "(s,t) \<in> (rfc_narrow_step R)\<^sup>*"
    unfolding rfc_forward_closure_def by auto
  from s_rhs obtain l where lr: "(l,s) \<in> set R" by auto
  from rfc_matchbox_closed_impl_rhss_word[OF closed s_rhs]
  obtain sw sx where s_word: "s = rfc_word_term sw sx" by blast
  from rfc_initial_paired_accepted_rhss[OF inv covers initial_acc lr]
  obtain q qf where q_tail: "q \<in> set tails"
    and qf: "qf \<in> ta_final (ta_of TAi)"
    and source_acc: "qf \<in> ta_res (ta_of TAi)
      (map_vars_term (\<lambda>_. q) (lift_term 0 s))"
    by blast
  have q_state: "q \<in> ta_states (ta_of TAi)"
    using tails_final q_tail unfolding ta_states_def by auto
  from rfc_matchbox_narrow_steps_accepted[
      OF inv state_cover coh closed ext_right s_word _ steps q_tail q_state]
  show ?thesis using q_tail qf source_acc by blast
qed

lemma rfc_native_matchbox_paired_forward_closure_accepted:
  fixes TAi :: "('q :: linorder,'f :: linorder \<times> nat) ta_impl"
  assumes inv: "ta_inv TAi (rel_checker Id_Relation) Id"
    and state_cover: "ta_states (ta_of TAi) \<subseteq> set qs"
    and closed: "rfc_native_matchbox_closed_impl
      TAi Id_Relation qs R"
    and ext_right: "rfc_native_matchbox_ext_right_impl
      TAi Id_Relation qs R"
    and wf: "wf_trs (set R)"
    and covers: "rfc_initial_covers R I"
    and initial_acc: "rfc_initial_paired_accepted_impl TYPE('f) TAi tails I"
    and tails_final: "set tails \<subseteq> ta_final (ta_of TAi)"
    and t: "t \<in> rfc_forward_closure R"
  shows "\<exists>q\<in>set tails. \<exists>qf\<in>ta_final (ta_of TAi).
    qf \<in> ta_res (ta_of TAi) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
proof -
  have old_closed: "rfc_matchbox_closed_impl
      TAi Id_Relation qs R"
    by (rule rfc_native_matchbox_closed_Id_imp[
      OF inv state_cover closed wf])
  have old_ext: "rfc_matchbox_ext_right_impl
      TAi Id_Relation tails qs R"
    by (rule rfc_native_matchbox_ext_right_Id_imp[
      OF inv state_cover ext_right])
  have coh: "state_coherent (ta_of TAi) Id"
    by (rule state_coherent_Id)
  have inv': "ta_inv TAi (rel_checker Id_Relation)
      (relation_of Id_Relation)"
    using inv by simp
  have coh': "state_coherent (ta_of TAi) (relation_of Id_Relation)"
    using coh by simp
  show ?thesis
    by (rule rfc_matchbox_paired_forward_closure_accepted[
      OF inv' state_cover coh' old_closed old_ext
        covers initial_acc tails_final t])
qed

lemma rfc_narrows_impl_imp_rstep_instance:
  assumes u: "u \<in> set (rfc_narrows_impl R s)"
  shows "\<exists>\<mu>. (s \<cdot> \<mu>, u) \<in> rstep (set R)"
proof -
  from u obtain p l r \<mu>1 \<mu>2 where
    p: "p \<in> poss s"
    and lr: "(l,r) \<in> set R"
    and mgu: "mgu_vd_string (s |_ p) l = Some (\<mu>1,\<mu>2)"
    and u_def: "u = replace_at (s \<cdot> \<mu>1) p (r \<cdot> \<mu>2)"
    unfolding rfc_narrows_impl by auto
  from mgu_vd_string_sound[OF mgu] have id: "s |_ p \<cdot> \<mu>1 = l \<cdot> \<mu>2"
    by simp
  have p_mu: "p \<in> poss (s \<cdot> \<mu>1)"
    using p by auto
  have id': "s \<cdot> \<mu>1 |_ p = l \<cdot> \<mu>2"
    using id unfolding subt_at_subst[OF p] .
  have "(s \<cdot> \<mu>1, u) \<in> rstep_r_p_s (set R) (l,r) p \<mu>2"
    unfolding rstep_r_p_s_def' u_def
    using lr p_mu id' by auto
  then have "(s \<cdot> \<mu>1, u) \<in> rstep (set R)"
    by (rule rstep_r_p_s_imp_rstep)
  then show ?thesis by blast
qed

lemma linear_rel_bound_SN_on:
  assumes lin: "\<exists>c. \<forall>n s t. s \<in> L \<longrightarrow> (s, t) \<in> R ^^ n \<longrightarrow> n \<le> term_size s * c"
  shows "SN_on R L"
proof
  fix f
  assume f0: "f 0 \<in> L" and ch: "\<forall>i. (f i, f (Suc i)) \<in> R"
  from lin obtain c where lin: "\<And>n s t. s \<in> L \<Longrightarrow> (s, t) \<in> R ^^ n \<Longrightarrow>
    n \<le> term_size s * c"
    by blast
  have steps: "(f 0, f n) \<in> R ^^ n" for n
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    moreover from ch have "(f n, f (Suc n)) \<in> R"
      by auto
    ultimately show ?case
      by auto
  qed
  let ?n = "Suc (term_size (f 0) * c)"
  have le: "?n \<le> term_size (f 0) * c"
    by (rule lin[OF f0 steps])
  have "term_size (f 0) * c < ?n" by simp
  with le show False by simp
qed

lemma narrow_steps_to_infinite_rel_rsteps:
  fixes D K :: "('f,'v::infinite)trs"
  defines "U \<equiv> D \<union> K"
  assumes wf: "wf_trs U"
    and s0: "s 0 = r"
    and steps: "\<And>i. (s i, s (Suc i)) \<in> narrow_step_s ren U (\<mu> i)"
    and delta: "\<And>i. \<delta> i = \<mu> i \<circ>\<^sub>s \<delta> (Suc i)"
    and infD: "INFM i. (s i, s (Suc i)) \<in> narrow_step_s ren D (\<mu> i)"
  shows "\<not> SN_on (relto (rstep D) (rstep K)) ((narrow_step ren U)\<^sup>* `` {r})"
proof -
  define \<gamma> where "\<gamma> = rec_nat Var (\<lambda>i \<gamma>. \<gamma> \<circ>\<^sub>s \<mu> i)"
  have \<gamma>: "\<gamma> 0 = Var" "\<And>i. \<gamma> (Suc i) = \<gamma> i \<circ>\<^sub>s \<mu> i"
    unfolding \<gamma>_def by auto
  define t0 where "t0 = r \<cdot> \<delta> 0"
  have delta0: "\<delta> 0 = \<gamma> i \<circ>\<^sub>s \<delta> i" for i
  proof (induct i)
    case (Suc i)
    then show ?case by (simp add: delta[of i] \<gamma> subst_compose_assoc)
  qed (auto simp: \<gamma>)
  have rstepsU: "(s i \<cdot> \<mu> i, s (Suc i)) \<in> rstep U" for i
    using narrow_step_s_to_rstep[OF steps[of i]] .
  have rstepsD: "(s i \<cdot> \<mu> i, s (Suc i)) \<in> rstep D"
    if "(s i, s (Suc i)) \<in> narrow_step_s ren D (\<mu> i)" for i
    using narrow_step_s_to_rstep[OF that] .
  have vars_si: "vars_term (s i \<cdot> \<mu> i) \<supseteq> vars_term (s (Suc i))" for i
  proof (rule rstep_vars_term[OF _ rstepsU[of i]])
    fix lr
    assume "lr \<in> U"
    with wf show "vars_term (fst lr) \<supseteq> vars_term (snd lr)"
      unfolding wf_trs_def by auto
  qed
  have subst0: "t0 = r \<cdot> \<gamma> i \<cdot> \<delta> i" for i
    unfolding t0_def delta0[of i] by simp
  have vars: "vars_term (s i) \<subseteq> vars_term (r \<cdot> \<gamma> i)" for i
  proof (induct i)
    case 0
    then show ?case by (auto simp: s0 \<gamma>)
  next
    case (Suc i)
    with vars_si[of i] show ?case
      by (force simp: vars_term_subst \<gamma>)
  qed
  define meas_fun where "meas_fun i = size (funs_term_ms (r \<cdot> \<gamma> i))" for i
  define dmeas_fun where "dmeas_fun i = size (funs_term_ms t0) - meas_fun i" for i
  have dmeas:
    "dmeas_fun (Suc i) \<le> dmeas_fun i"
    "\<exists>x\<in>vars_term (s i). is_Fun (\<mu> i x) \<Longrightarrow> dmeas_fun (Suc i) < dmeas_fun i"
    for i
  proof -
    define rg where "rg = r \<cdot> \<gamma> i"
    let ?diff = "\<Sum>\<^sub># ((funs_term_ms \<circ>\<circ> \<mu>) i `# vars_term_ms rg)"
    have bnd: "meas_fun (Suc i) \<le> size (funs_term_ms t0)"
      unfolding subst0[of "Suc i"] meas_fun_def funs_term_ms_subst_apply by simp
    have "funs_term_ms (r \<cdot> \<gamma> (Suc i)) = funs_term_ms (rg \<cdot> \<mu> i)"
      unfolding \<gamma> rg_def by simp
    also have "\<dots> = funs_term_ms rg + sum_mset ((funs_term_ms o \<mu> i) `# vars_term_ms rg)"
      unfolding funs_term_ms_subst_apply o_def by simp
    finally have id: "funs_term_ms (r \<cdot> \<gamma> (Suc i)) = funs_term_ms rg + ?diff"
      by auto
    from arg_cong[OF this, of size]
    have meas: "meas_fun (Suc i) = meas_fun i + size ?diff"
      by (auto simp: meas_fun_def rg_def)
    then show "dmeas_fun (Suc i) \<le> dmeas_fun i"
      using bnd unfolding dmeas_fun_def by auto
    assume "\<exists>x\<in>vars_term (s i). is_Fun (\<mu> i x)"
    with vars[of i, unfolded rg_def[symmetric]]
    obtain x where x: "x \<in># vars_term_ms rg" and f: "is_Fun (\<mu> i x)" by auto
    then obtain xs where vars_rg: "vars_term_ms rg = add_mset x xs"
      by (metis mset_add)
    with f have diff_pos: "size ?diff > 0"
      by (cases "\<mu> i x", auto)
    from meas bnd diff_pos show "dmeas_fun (Suc i) < dmeas_fun i"
      unfolding dmeas_fun_def by linarith
  qed
  have "\<exists>j. \<forall>i\<ge>j.
      (dmeas_fun i, dmeas_fun (Suc i)) \<in> {(x,y). y \<le> x} - {(x,y). y < x}"
    by (rule non_strict_ending[of dmeas_fun], insert dmeas SN_nat_gt, auto simp: SN_defs)
  then obtain j where dmeas_eq: "\<And>i. i \<ge> j \<Longrightarrow> dmeas_fun (Suc i) = dmeas_fun i"
    by fastforce
  have muVar: "\<mu> i ` vars_term (s i) \<subseteq> range Var" if "i \<ge> j" for i
    using dmeas_eq[OF that] dmeas(2)[of i] by force
  have "\<forall>i. \<exists>\<mu>'. i \<ge> j \<longrightarrow> s i \<cdot> \<mu> i = s i \<cdot> (Var o \<mu>')"
  proof
    fix i
    show "\<exists>\<mu>'. i \<ge> j \<longrightarrow> s i \<cdot> \<mu> i = s i \<cdot> (Var o \<mu>')"
    proof (cases "i \<ge> j")
      case True
      from muVar[OF True] have "\<forall>x. \<exists>y. x \<in> vars_term (s i) \<longrightarrow> \<mu> i x = Var y"
        by auto
      from choice[OF this] obtain \<mu>i where "\<And>x. x \<in> vars_term (s i) \<Longrightarrow> \<mu> i x = Var (\<mu>i x)"
        by auto
      then have "s i \<cdot> \<mu> i = s i \<cdot> (Var o \<mu>i)"
        by (intro term_subst_eq, auto)
      then show ?thesis by auto
    qed auto
  qed
  from choice[OF this] obtain \<mu>' where
    \<mu>': "\<And>i. i \<ge> j \<Longrightarrow> s i \<cdot> \<mu> i = s i \<cdot> (Var o (\<mu>' i))"
    by blast
  define vs where "vs i = vars_term (s (i + j) \<cdot> \<mu> (i + j))" for i
  have fin_vs[simp,intro]: "finite (vs i)" for i
    unfolding vs_def by auto
  define meas_var where "meas_var i = card (vs i)" for i
  have meas_var:
    "vs (Suc i) \<subseteq> \<mu>' (Suc i + j) ` vs i"
    "meas_var (Suc i) \<le> meas_var i"
    for i
  proof -
    have "vs (Suc i) = \<mu>' (Suc (i + j)) ` vars_term (s (Suc (i + j)))"
      using \<mu>'[of "Suc (i + j)"] unfolding vs_def
      by (auto simp: vars_term_subst)
    also have "\<dots> \<subseteq> \<mu>' (Suc (i + j)) ` vs i"
      using vars_si[of "i + j"] unfolding vs_def by auto
    finally show sub: "vs (Suc i) \<subseteq> \<mu>' (Suc i + j) ` vs i"
      by auto
    from card_mono[OF finite_imageI[OF fin_vs] sub]
    show "meas_var (Suc i) \<le> meas_var i"
      unfolding meas_var_def using card_image_le[OF fin_vs] by (metis le_trans)
  qed
  have "\<exists>k. \<forall>i\<ge>k.
      (meas_var i, meas_var (Suc i)) \<in> {(x,y). y \<le> x} - {(x,y). y < x}"
    by (rule non_strict_ending[of meas_var], insert meas_var SN_nat_gt, auto simp: SN_defs)
  then obtain k where meas_var_eq: "\<And>i. i \<ge> k \<Longrightarrow> meas_var (Suc i) = meas_var i"
    by fastforce
  define l where "l = Suc k + j"
  have inj: "inj_on (\<mu>' ii) (vars_term (s ii))" if "ii \<ge> l" for ii
  proof -
    define i where "i = ii - Suc 0"
    define i' where "i' = i - j"
    have ij: "i \<ge> k + j" and ii: "ii = Suc i" and iij: "ii \<ge> j"
      using that unfolding l_def i_def by auto
    then have i: "i = i' + j" "Suc i' + j = Suc i" "i' \<ge> k"
      unfolding i'_def by auto
    from meas_var_eq[OF i(3), unfolded meas_var_def]
    have card: "card (vs (Suc i')) = card (vs i')" by auto
    from meas_var(1)[of i', unfolded i(2)]
    have "vs (Suc i') \<subseteq> \<mu>' (Suc i) ` vs i'" by auto
    with card have "inj_on (\<mu>' (Suc i)) (vs i')"
      by (metis card_image_le card_seteq eq_card_imp_inj_on fin_vs finite_imageI)
    then show ?thesis
      using vars_si[of i] unfolding vs_def i(1)[symmetric] ii
      by (metis inj_on_subset)
  qed
  define sl where "sl i = s (i + l)" for i
  have tail_step:
    "\<exists>\<rho>. (sl i, sl (Suc i) \<cdot> \<rho>) \<in> rstep U \<and>
      ((s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))
        \<longrightarrow> (sl i, sl (Suc i) \<cdot> \<rho>) \<in> rstep D)"
    for i
  proof -
    have ii_l: "i + l \<ge> l" by simp
    have ii_j: "i + l \<ge> j" using ii_l unfolding l_def by auto
    from inj[OF ii_l] obtain inv where inv:
      "\<And>x. x \<in> vars_term (s (i + l)) \<Longrightarrow> inv ((\<mu>' (i + l)) x) = x"
      by (metis the_inv_into_f_f)
    have back_subst: "(s (i + l) \<cdot> (\<mu> (i + l))) \<cdot> (Var o inv) = s (i + l)"
    proof -
      have "(s (i + l) \<cdot> (\<mu> (i + l))) \<cdot> (Var o inv) =
          s (i + l) \<cdot> ((Var o \<mu>' (i + l)) \<circ>\<^sub>s (Var o inv))"
        using \<mu>'[OF ii_j] by simp
      also have "\<dots> = s (i + l) \<cdot> Var"
        by (rule term_subst_eq, insert inv, auto simp: o_def subst_compose_def)
      finally show ?thesis by simp
    qed
    from rstep_subst[OF rstepsU[of "i + l"], of "Var o inv", unfolded back_subst]
    have stepU: "(sl i, sl (Suc i) \<cdot> (Var o inv)) \<in> rstep U"
      unfolding sl_def by simp
    have stepD: "(sl i, sl (Suc i) \<cdot> (Var o inv)) \<in> rstep D"
      if "(s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))"
      using rstep_subst[OF rstepsD[OF that], of "Var o inv", unfolded back_subst]
      unfolding sl_def by simp
    show ?thesis
      by (intro exI[of _ "Var o inv"] conjI impI stepU stepD)
  qed
  have all_tail:
    "\<forall>i. \<exists>\<rho>. (sl i, sl (Suc i) \<cdot> \<rho>) \<in> rstep U \<and>
      ((s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))
        \<longrightarrow> (sl i, sl (Suc i) \<cdot> \<rho>) \<in> rstep D)"
    using tail_step by blast
  from choice[OF all_tail]
  obtain \<rho> where tail:
    "\<And>i. (sl i, sl (Suc i) \<cdot> \<rho> i) \<in> rstep U \<and>
      ((s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))
        \<longrightarrow> (sl i, sl (Suc i) \<cdot> \<rho> i) \<in> rstep D)"
    by blast
  have tailU: "\<And>i. (sl i, sl (Suc i) \<cdot> \<rho> i) \<in> rstep U"
    using tail by blast
  have tailD: "\<And>i. (s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))
      \<Longrightarrow> (sl i, sl (Suc i) \<cdot> \<rho> i) \<in> rstep D"
    using tail by blast
  define \<rho>' where "\<rho>' = rec_nat Var (\<lambda>i gam. \<rho> i \<circ>\<^sub>s gam)"
  define ts where "ts i = sl i \<cdot> \<rho>' i" for i
  have tailU': "(ts i, ts (Suc i)) \<in> rstep U" for i
    unfolding ts_def \<rho>'_def using rstep_subst[OF tailU[of i]] by simp
  have tailD': "(ts i, ts (Suc i)) \<in> rstep D"
    if "(s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))" for i
    unfolding ts_def \<rho>'_def using rstep_subst[OF tailD[OF that]] by simp
  have steps_rel: "\<And>i. (ts i, ts (Suc i)) \<in> rstep D \<union> rstep K"
    using tailU' unfolding U_def rstep_union by auto
  have inf_rel: "INFM i. (ts i, ts (Suc i)) \<in> rstep D"
  proof -
    have "INFM i. (s (i + l), s (Suc (i + l))) \<in> narrow_step_s ren D (\<mu> (i + l))"
      unfolding INFM_nat_le
    proof
      fix m
      from infD[unfolded INFM_nat_le] obtain n where n: "n \<ge> m + l"
        and step: "(s n, s (Suc n)) \<in> narrow_step_s ren D (\<mu> n)"
        by blast
      let ?k = "n - l"
      from n have "?k \<ge> m" and "n = ?k + l" by auto
      with step show "\<exists>k\<ge>m.
        (s (k + l), s (Suc (k + l))) \<in> narrow_step_s ren D (\<mu> (k + l))"
        by auto
    qed
    then show ?thesis
      unfolding INFM_nat_le using tailD' by metis
  qed
  have ts0_RFC: "ts 0 \<in> (narrow_step ren U)\<^sup>* `` {r}"
  proof -
    have "s l \<in> (narrow_step ren U)\<^sup>* `` {r}"
    proof (induct l)
      case 0
      then show ?case using s0 by auto
    next
      case (Suc i)
      from steps[of i] have "(s i, s (Suc i)) \<in> narrow_step ren U"
        unfolding narrow_step_to_s by auto
      with Suc show ?case by (metis rtrancl_image_advance)
    qed
    then show ?thesis unfolding ts_def sl_def \<rho>'_def by simp
  qed
  show ?thesis
    unfolding SN_rel_on_def[symmetric] SN_rel_on_conv SN_rel_on_alt_def
    by (intro notI, drule spec[of _ ts], insert ts0_RFC steps_rel inf_rel, auto)
qed

lemma nrrsteps_imp_rsteps_union:
  assumes "(s,t) \<in> (nrrstep (R \<union> E))\<^sup>*"
  shows "(s,t) \<in> (rstep R \<union> rstep E)\<^sup>*"
proof -
  have "nrrstep (R \<union> E) \<subseteq> rstep R \<union> rstep E"
    unfolding nrrstep_union using nrrstep_imp_rstep by auto
  from rtrancl_mono[OF this] assms show ?thesis by auto
qed

lemma not_SN_on_rel_preds:
  assumes steps: "(s,t) \<in> (R \<union> E)\<^sup>*"
    and nSN: "\<not> SN_on (relto R E) {t}"
  shows "\<not> SN_on (relto R E) {s}"
  using steps nSN
proof (induct rule: converse_rtrancl_induct)
  case base
  then show ?case .
next
  case (step s u)
  have nSN_u: "\<not> SN_on (relto R E) {u}" by (rule step(3)[OF step(4)])
  show ?case
  proof
    assume "SN_on (relto R E) {s}"
    from step_preserves_SN_on_relto[OF step(1) this]
    show False using nSN_u by auto
  qed
qed

lemma Tinf_nrrsteps:
  assumes tinf: "s \<in> Tinf (relstep R E)"
    and steps: "(s,t) \<in> (nrrstep (R \<union> E))\<^sup>*"
    and nSN: "\<not> SN_on (relstep R E) {t}"
  shows "t \<in> Tinf (relstep R E)"
  using steps tinf
proof (induct rule: converse_rtrancl_induct)
  case base
  then show ?case .
next
  case (step s u)
  have u_t: "(u,t) \<in> (rstep R \<union> rstep E)\<^sup>*"
    by (rule nrrsteps_imp_rsteps_union[OF step(2)])
  have nSN_u: "\<not> SN_on (relstep R E) {u}"
    by (rule not_SN_on_rel_preds[OF u_t nSN])
  have u_tinf: "u \<in> Tinf (relstep R E)"
    by (rule Tinf_nrrstep[OF step(4) step(1) nSN_u])
  from step(3)[OF u_tinf] show ?case .
qed

lemma Tinf_relstep_imp_first_root_step:
  assumes tinf: "s \<in> Tinf (relstep R E)"
  shows "\<exists>t u. (s,t) \<in> (nrrstep (R \<union> E))\<^sup>* \<and>
    (t,u) \<in> rrstep (R \<union> E) \<and> t \<in> Tinf (relstep R E) \<and>
    \<not> SN_on (relstep R E) {u}"
proof -
  from Tinf_imp_SN_nr_first_root_step_rel[
      of s False "{}" E "{}" R,
      unfolded qrstep_rstep_conv nrqrstep_nrrstep rqrstep_rrstep_conv
        nrrstep_union[symmetric] rrstep_union[symmetric],
      OF tinf]
  obtain t u where st: "(s,t) \<in> (nrrstep (R \<union> E))\<^sup>*"
    and tu: "(t,u) \<in> rrstep (R \<union> E)"
    and nSN_u: "\<not> SN_on (relstep R E) {u}"
    by auto
  have tu_step: "(t,u) \<in> rstep R \<union> rstep E"
    using tu unfolding rrstep_union rstep_iff_rrstep_or_nrrstep by auto
  have nSN_t: "\<not> SN_on (relstep R E) {t}"
    by (rule not_SN_on_rel_preds[OF _ nSN_u], insert tu_step, auto)
  have t_tinf: "t \<in> Tinf (relstep R E)"
    by (rule Tinf_nrrsteps[OF tinf st nSN_t])
  show ?thesis using st tu t_tinf nSN_u by blast
qed

(* A general RFC equivalence theorem for relative rewriting needs a proper
   treatment of weak steps between strict steps.  The executable checker below
   uses the certified automaton-closed relative match-bounds semantics directly
   and combines it with the standard qrel split processor. *)
 (*
lemma right_forw_closure_SN_rel_main:
  fixes D K :: "('f,'v::infinite)trs"
  assumes right_lin: "\<And>lr. lr \<in> D \<union> K \<Longrightarrow> linear_term (snd lr)"
    and wf: "wf_trs (D \<union> K)"
    and nSN: "\<not> SN_rel (rstep D) (rstep K)"
  shows "\<not> SN_on (relto (rstep D) (rstep K)) (right_forw_closure ren (D \<union> K))"
proof -
  let ?U = "D \<union> K"
  let ?D = "rstep D"
  let ?K = "rstep K"
  let ?REL = "relto ?D ?K"
  let ?N = "narrow_step ren ?U"
  let ?NSU = "narrow_step_s ren ?U"
  let ?NSD = "narrow_step_s ren D"
  let ?RFC = "right_forw_closure ren ?U"
  have var_cond: "\<And>lr. lr \<in> ?U \<Longrightarrow> vars_term (snd lr) \<subseteq> vars_term (fst lr)"
  proof -
    fix lr
    assume lr: "lr \<in> ?U"
    obtain l r where [simp]: "lr = (l,r)" by (cases lr, auto)
    from wf lr show "vars_term (snd lr) \<subseteq> vars_term (fst lr)"
      by (auto simp: wf_trs_def)
  qed
  have var_condD: "\<And>lr. lr \<in> D \<Longrightarrow> vars_term (snd lr) \<subseteq> vars_term (fst lr)"
    using var_cond by auto
  have right_linD: "\<And>lr. lr \<in> D \<Longrightarrow> linear_term (snd lr)"
    using right_lin by auto
  from nSN obtain t where nSNt: "\<not> SN_on ?REL {t}"
    unfolding SN_rel_on_def SN_defs by auto
  from not_SN_imp_subt_Tinf[OF nSNt] obtain t where Tinf: "t \<in> Tinf ?REL"
    by auto
  from Tinf_relstep_imp_first_root_step[OF Tinf]
  obtain tm1 t0 where Tinf_tm1: "tm1 \<in> Tinf ?REL"
    and root: "(tm1,t0) \<in> rrstep ?U"
    and nt0: "\<not> SN_on ?REL {t0}"
    by auto
  from rrstepE[OF root] obtain l r0 \<sigma>0
    where lr: "(l,r0) \<in> ?U" and tm1: "tm1 = l \<cdot> \<sigma>0" and t0: "t0 = r0 \<cdot> \<sigma>0"
    by blast
  have r0_rfc: "r0 \<in> ?RFC"
    using lr unfolding right_forw_closure_def by auto
  have linr: "linear_term r0"
    using right_lin[OF lr] by simp
  define SNT where "SNT = {t. SN_on ?REL {t}}"
  define stm :: "('f,'v)term \<Rightarrow> _" where "stm = subst_term_mset"
  have sig_SNT: "\<And>x. x \<in> vars_term r0 \<Longrightarrow> \<sigma>0 x \<in> SNT"
  proof -
    fix x
    assume x: "x \<in> vars_term r0"
    with var_cond[OF lr] have xl: "x \<in> vars_term l" by auto
    from wf lr obtain f ls where l: "l = Fun f ls"
      by (cases l, auto simp: wf_trs_def)
    with xl obtain li where li: "li \<in> set ls" and xli: "x \<in> vars_term li" by auto
    then have subt: "li \<cdot> \<sigma>0 \<unrhd> \<sigma>0 x"
      by (metis eval_term.simps(1) supteq_subst vars_term_supteq)
    have top_subt: "Fun f ls \<cdot> \<sigma>0 \<rhd> li \<cdot> \<sigma>0"
      using li by auto
    from top_subt subt have "tm1 \<rhd> \<sigma>0 x"
      unfolding tm1 l by (rule supt_supteq_trans)
    with Tinf_tm1[unfolded Tinf_def] have "SN_on ?REL {\<sigma>0 x}" by auto
    then show "\<sigma>0 x \<in> SNT" unfolding SNT_def by auto
  qed
  have r0_SNT: "set_mset (stm r0 \<sigma>0) \<subseteq> SNT"
    using sig_SNT unfolding subst_term_mset_def stm_def by auto
  define Rel where "Rel = restrict_SN_supt ?REL"
  define mRel where "mRel = mult (Rel^-1)"
  have ctxt_REL: "ctxt.closed ?REL"
    by (rule ctxt.closed_relto, auto)
  have SN_Rel: "SN Rel"
    unfolding Rel_def by (rule ctxt_closed_imp_SN_restrict_SN_supt[OF ctxt_REL])
  then have wf_mRel: "wf mRel"
    unfolding mRel_def by (simp add: SN_imp_wf wf_mult)
  have U_SNT: "\<And>u v. (u,v) \<in> rstep ?U \<Longrightarrow> u \<in> SNT \<Longrightarrow> v \<in> SNT"
  proof -
    fix u v
    assume uv: "(u,v) \<in> rstep ?U" and u: "u \<in> SNT"
    have uv_DK: "(u,v) \<in> ?D \<union> ?K" using uv unfolding rstep_union by auto
    have uSN: "SN_on ?REL {u}" using u unfolding SNT_def by simp
    from step_preserves_SN_on_relto[where R = ?D and E = ?K, OF uv_DK uSN]
    show "v \<in> SNT" unfolding SNT_def by simp
  qed
  have supt_SNT: "\<And>u v. u \<rhd> v \<Longrightarrow> u \<in> SNT \<Longrightarrow> v \<in> SNT"
  proof -
    fix u v
    assume uv: "u \<rhd> v" and u: "u \<in> SNT"
    have uSN: "SN_on ?REL {u}" using u unfolding SNT_def by simp
    have uv_eq: "u \<unrhd> v" using uv by (rule supt_imp_supteq)
    from ctxt_closed_SN_on_subt[OF ctxt_REL uSN uv_eq]
    show "v \<in> SNT" unfolding SNT_def by simp
  qed
  have rstepD_into_mRel:
    "set_mset (stm s \<sigma>) \<subseteq> SNT \<Longrightarrow>
      (stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep D)\<inverse>) \<Longrightarrow>
      set_mset (stm s \<delta>) \<subseteq> SNT \<and> (stm s \<delta>, stm s \<sigma>) \<in> mRel"
    for s \<sigma> \<delta>
  proof -
    assume SNT: "set_mset (stm s \<sigma>) \<subseteq> SNT"
      and decr: "(stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep D)\<inverse>)"
    have SNT': "set_mset (stm s \<delta>) \<subseteq> SNT"
    proof
      fix u
      assume "u \<in># stm s \<delta>"
      with decr obtain v where v: "v \<in># stm s \<sigma>" and disj: "u = v \<or> (v,u) \<in> rstep ?U"
        unfolding mult1_def by force
      from SNT v have "v \<in> SNT" by auto
      with U_SNT[of v u] disj show "u \<in> SNT" by auto
    qed
    from decr[unfolded mult1_def, simplified]
    obtain t M K' where split: "stm s \<sigma> = add_mset t M" "stm s \<delta> = M + K'"
	      and steps: "\<And>u. u \<in># K' \<Longrightarrow> (t,u) \<in> rstep D"
      by auto
	    have rel_steps: "\<And>u. u \<in># K' \<Longrightarrow> (u,t) \<in> Rel^-1"
	    proof -
	      fix u
	      assume u: "u \<in># K'"
	      have rel: "(t,u) \<in> ?REL"
	        using steps[OF u] by (metis relcompI rtrancl.rtrancl_refl)
	      from split SNT SNT' u rel show "(u,t) \<in> Rel^-1"
	        unfolding Rel_def restrict_SN_supt_def restrict_SN_def SNT_def by auto
	    qed
	    have "(stm s \<delta>, stm s \<sigma>) \<in> mult1 (Rel^-1)"
	      unfolding mult1_def split
	      using rel_steps by blast
    then show ?thesis using SNT' unfolding mRel_def by (auto simp: mult_def)
  qed
  have tr: "trans {\<lhd>}" by (simp add: trans_supt)
  have supt_into_mRel:
    "set_mset (stm t \<sigma>) \<subseteq> SNT \<Longrightarrow>
      (stm s \<delta>, stm t \<sigma>) \<in> mult {\<lhd>} \<Longrightarrow>
      set_mset (stm s \<delta>) \<subseteq> SNT \<and> (stm s \<delta>, stm t \<sigma>) \<in> mRel"
    for s t \<sigma> \<delta>
  proof -
    assume SNT: "set_mset (stm t \<sigma>) \<subseteq> SNT"
      and decr: "(stm s \<delta>, stm t \<sigma>) \<in> mult {\<lhd>}"
    from mult_implies_one_step[OF tr decr] obtain I J K'
      where split: "stm t \<sigma> = I + J" "stm s \<delta> = I + K'"
        and J: "J \<noteq> {#}" and step: "\<And>k. k\<in>#K' \<Longrightarrow> \<exists>j\<in>#J. k \<lhd> j"
      by auto
    have SNT': "set_mset (stm s \<delta>) \<subseteq> SNT"
    proof
      fix u
      assume "u \<in># stm s \<delta>"
      then obtain v where "v \<in># stm t \<sigma>" "u = v \<or> v \<rhd> u"
        unfolding split using step by auto
      with supt_SNT SNT show "u \<in> SNT" by auto
    qed
	    have rel_sub: "\<forall>k\<in>#K'. \<exists>j\<in>#J. (k,j) \<in> Rel^-1"
	    proof
	      fix k
	      assume k: "k \<in># K'"
	      from step[OF k] obtain j where j: "j \<in># J" "j \<rhd> k" by auto
	      from SNT j have snj: "j \<in> SNT" by (auto simp: split)
	      have "(j,k) \<in> Rel"
	        using j snj unfolding Rel_def restrict_SN_supt_def restrict_SN_def SNT_def by auto
	      with j show "\<exists>j\<in>#J. (k,j) \<in> Rel^-1" by auto
	    qed
	    have "(stm s \<delta>, stm t \<sigma>) \<in> mRel"
	      unfolding split mRel_def
	      by (rule one_step_implies_mult[OF J, of K' "Rel^-1" I], rule rel_sub)
    then show ?thesis using SNT' by auto
  qed
  define P where "P s \<sigma> = (linear_term s \<and> set_mset (stm s \<sigma>) \<subseteq> SNT \<and> s \<in> ?RFC)" for s \<sigma>
  define narr_step :: "('f,'v)trs \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)subst \<Rightarrow>
      ('f,'v)term \<Rightarrow> ('f,'v)subst \<Rightarrow> ('f,'v)subst \<Rightarrow> bool"
    where "narr_step X s \<sigma> u \<mu> \<delta> =
      ((s,u) \<in> narrow_step_s ren X \<mu> \<and> \<sigma> = \<mu> \<circ>\<^sub>s \<delta>)"
    for X s \<sigma> u \<mu> \<delta>
  from nt0[unfolded SN_rel_on_def[symmetric] SN_rel_on_conv SN_rel_on_alt_def]
  obtain ts where ts0: "ts 0 = t0"
    and raw_steps: "\<And>i. (ts i, ts (Suc i)) \<in> ?D \<union> ?K"
    and raw_infD: "INFM i. (ts i, ts (Suc i)) \<in> ?D"
    by auto
  define step_cond where "step_cond i s \<sigma> u \<delta> = (ts (Suc i) = u \<cdot> \<delta> \<and>
      P u \<delta> \<and> ((stm u \<delta>, stm s \<sigma>) \<in> mRel \<or>
        stm u \<delta> = stm s \<sigma> \<and>
          (\<exists>\<mu>. narr_step ?U s \<sigma> u \<mu> \<delta> \<and>
             ((ts i, ts (Suc i)) \<in> ?D \<longrightarrow> narr_step D s \<sigma> u \<mu> \<delta>))))"
    for i s \<sigma> u \<delta>
  have simu: "\<And>i s \<sigma>. s \<cdot> \<sigma> = ts i \<Longrightarrow> P s \<sigma> \<Longrightarrow>
      \<exists>u \<delta>. step_cond i s \<sigma> u \<delta>"
  proof -
    fix i s \<sigma>
    assume s_ts: "s \<cdot> \<sigma> = ts i" and Ps: "P s \<sigma>"
    from Ps have lin: "linear_term s" and SNT: "set_mset (stm s \<sigma>) \<subseteq> SNT"
      and RFC: "s \<in> ?RFC" unfolding P_def by auto
    from raw_steps[of i] have stepU: "(s \<cdot> \<sigma>, ts (Suc i)) \<in> rstep ?U"
      using s_ts unfolding rstep_union by auto
    show "\<exists>u \<delta>. step_cond i s \<sigma> u \<delta>"
    proof (cases "(ts i, ts (Suc i)) \<in> ?D")
      case True
      then have stepD: "(s \<cdot> \<sigma>, ts (Suc i)) \<in> rstep D" using s_ts by simp
      from narrowing_right_linear_one_step_simulation[of _ _ _ D ren, OF stepD lin right_linD var_condD]
      consider (decr) \<delta> where "ts (Suc i) = s \<cdot> \<delta>"
          "(stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep D)\<inverse>)"
        | (narrow) \<mu> \<delta> u where "ts (Suc i) = u \<cdot> \<delta>" "linear_term u"
          "(s,u) \<in> ?NSD \<mu>" "\<sigma> = \<mu> \<circ>\<^sub>s \<delta>"
          "(stm u \<delta>, stm s \<sigma>) \<in> (mult {\<lhd>})\<^sup>="
        unfolding stm_def by auto
      then show ?thesis
      proof cases
        case (decr \<delta>)
        then have t: "ts (Suc i) = s \<cdot> \<delta>"
          and decrD: "(stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep D)\<inverse>)" by auto
        from rstepD_into_mRel[OF SNT decrD]
        have SNTd: "set_mset (stm s \<delta>) \<subseteq> SNT"
          and m: "(stm s \<delta>, stm s \<sigma>) \<in> mRel" by auto
        have Ps_delta: "P s \<delta>"
          unfolding P_def using lin SNTd RFC by simp
        show ?thesis
          using t Ps_delta m unfolding step_cond_def by auto
      next
        case (narrow \<mu> \<delta> u)
        then have t: "ts (Suc i) = u \<cdot> \<delta>" and linu: "linear_term u"
          and nsD: "(s,u) \<in> ?NSD \<mu>" and comp: "\<sigma> = \<mu> \<circ>\<^sub>s \<delta>"
          and decr: "(stm u \<delta>, stm s \<sigma>) \<in> (mult {\<lhd>})\<^sup>=" by auto
        have nsU: "(s,u) \<in> ?NSU \<mu>"
          using nsD unfolding narrow_step_s_def narrows_r_p_s_def by force
        have nD: "narr_step D s \<sigma> u \<mu> \<delta>"
          using nsD comp unfolding narr_step_def by auto
        have nU: "narr_step ?U s \<sigma> u \<mu> \<delta>"
          using nsU comp unfolding narr_step_def by auto
        have ns_step: "(s,u) \<in> ?N"
          using nsU unfolding narrow_step_def narrow_step_s_def by blast
        have RFCu: "u \<in> ?RFC"
        proof -
          from RFC obtain r where r: "r \<in> rhss ?U" "(r,s) \<in> ?N\<^sup>*"
            unfolding right_forw_closure_def by auto
          from r(2) ns_step have "(r,u) \<in> ?N\<^sup>*"
            by (rule rtrancl_into_rtrancl)
          with r(1) show ?thesis unfolding right_forw_closure_def by auto
        qed
        show ?thesis
        proof (cases "(stm u \<delta>, stm s \<sigma>) \<in> mult {\<lhd>}")
          case True
          from supt_into_mRel[OF SNT this]
          have SNTu: "set_mset (stm u \<delta>) \<subseteq> SNT"
            and m: "(stm u \<delta>, stm s \<sigma>) \<in> mRel" by auto
          have Pu: "P u \<delta>"
            unfolding P_def using linu SNTu RFCu by simp
          show ?thesis
            using t Pu m unfolding step_cond_def by auto
        next
          case False
          from decr False have eq: "stm u \<delta> = stm s \<sigma>" by auto
          have Pu: "P u \<delta>"
            unfolding P_def using linu RFCu SNT eq by simp
          have nar: "\<exists>\<mu>. narr_step ?U s \<sigma> u \<mu> \<delta> \<and>
             ((ts i, ts (Suc i)) \<in> ?D \<longrightarrow> narr_step D s \<sigma> u \<mu> \<delta>)"
            using nU nD by blast
          have sc: "step_cond i s \<sigma> u \<delta>"
            unfolding step_cond_def using t Pu eq nar by blast
          show ?thesis
            using sc by blast
        qed
      qed
    next
      case False
      from narrowing_right_linear_one_step_simulation[of _ _ _ ?U ren, OF stepU lin right_lin var_cond]
      show ?thesis
      proof
        assume "\<exists>\<delta>. ts (Suc i) = s \<cdot> \<delta> \<and>
          (stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep ?U)\<inverse>)"
        then obtain \<delta> where t: "ts (Suc i) = s \<cdot> \<delta>"
          and decr: "(stm s \<delta>, stm s \<sigma>) \<in> mult1 ((rstep ?U)\<inverse>)" by auto
        from rstep_into_mRel[OF SNT decr]
        have SNTd: "set_mset (stm s \<delta>) \<subseteq> SNT"
          and m: "(stm s \<delta>, stm s \<sigma>) \<in> mRel" by auto
        have Ps_delta: "P s \<delta>"
          unfolding P_def using lin SNTd RFC by simp
        from t Ps_delta m
        show ?thesis
          by (intro exI[of _ s] exI[of _ \<delta>], simp add: step_cond_def)
      next
        assume "\<exists>\<mu> \<delta> u. ts (Suc i) = u \<cdot> \<delta> \<and> linear_term u \<and>
          (s,u) \<in> ?NSU \<mu> \<and> \<sigma> = \<mu> \<circ>\<^sub>s \<delta> \<and>
          (stm u \<delta>, stm s \<sigma>) \<in> (mult {\<lhd>})\<^sup>="
        then obtain \<mu> \<delta> u where t: "ts (Suc i) = u \<cdot> \<delta>" and linu: "linear_term u"
          and nsU: "(s,u) \<in> ?NSU \<mu>" and comp: "\<sigma> = \<mu> \<circ>\<^sub>s \<delta>"
          and decr: "(stm u \<delta>, stm s \<sigma>) \<in> (mult {\<lhd>})\<^sup>=" by auto
        have nU: "narr_step ?U s \<sigma> u \<mu> \<delta>"
          using nsU comp unfolding narr_step_def by auto
        have ns_step: "(s,u) \<in> ?N"
          using nsU unfolding narrow_step_def narrow_step_s_def by blast
        have RFCu: "u \<in> ?RFC"
        proof -
          from RFC obtain r where r: "r \<in> rhss ?U" "(r,s) \<in> ?N\<^sup>*"
            unfolding right_forw_closure_def by auto
          from r(2) ns_step have "(r,u) \<in> ?N\<^sup>*"
            by (rule rtrancl_into_rtrancl)
          with r(1) show ?thesis unfolding right_forw_closure_def by auto
        qed
        from decr show ?thesis
        proof
          assume "(stm u \<delta>, stm s \<sigma>) \<in> mult {\<lhd>}"
          from supt_into_mRel[OF SNT this]
          have SNTu: "set_mset (stm u \<delta>) \<subseteq> SNT"
            and m: "(stm u \<delta>, stm s \<sigma>) \<in> mRel" by auto
          have Pu: "P u \<delta>"
            unfolding P_def using linu SNTu RFCu by simp
          from t Pu m
          show ?thesis
            by (intro exI[of _ u] exI[of _ \<delta>], simp add: step_cond_def)
        next
          assume eq: "stm u \<delta> = stm s \<sigma>"
          have Pu: "P u \<delta>"
            unfolding P_def using linu RFCu SNT eq by simp
          have nar: "\<exists>\<mu>. narr_step ?U s \<sigma> u \<mu> \<delta> \<and>
             ((ts i, ts (Suc i)) \<in> ?D \<longrightarrow> narr_step D s \<sigma> u \<mu> \<delta>)"
            using nU False by blast
          from t Pu eq nar show ?thesis
            by (intro exI[of _ u] exI[of _ \<delta>], simp add: step_cond_def)
        qed
      qed
    qed
  qed
  have P0: "P r0 \<sigma>0"
    unfolding P_def using linr r0_SNT r0_rfc by auto
  have start: "r0 \<cdot> \<sigma>0 = ts 0 \<and> P r0 \<sigma>0"
    using ts0 t0 P0 by auto
  have step_choice: "\<And>i s sig. s \<cdot> sig = ts i \<and> P s sig \<Longrightarrow>
      \<exists>u \<delta>. (u \<cdot> \<delta> = ts (Suc i) \<and> P u \<delta>) \<and> step_cond i s sig u \<delta>"
  proof -
    fix i s sig
    assume a: "s \<cdot> sig = ts i \<and> P s sig"
    from simu[OF conjunct1[OF a] conjunct2[OF a]]
    obtain u \<delta> where sc: "step_cond i s sig u \<delta>" by auto
    then have "u \<cdot> \<delta> = ts (Suc i)" "P u \<delta>"
      unfolding step_cond_def by auto
    with sc show "\<exists>u \<delta>. (u \<cdot> \<delta> = ts (Suc i) \<and> P u \<delta>) \<and> step_cond i s sig u \<delta>"
      by (intro exI[of _ u] exI[of _ \<delta>], simp)
  qed
  from dependent_nat_choice2_start[
      of "\<lambda>i s sig. s \<cdot> sig = ts i \<and> P s sig" r0 \<sigma>0
        "\<lambda>i p1 p2 q1 q2. step_cond i p1 p2 q1 q2",
      OF start step_choice]
  obtain rs sig where chain:
    "\<And>i. P (rs i) (sig i)"
    "\<And>i. rs i \<cdot> sig i = ts i"
    "\<And>i. step_cond i (rs i) (sig i) (rs (Suc i)) (sig (Suc i))"
    by blast
  define stmp where "stmp i = stm (rs i) (sig i)" for i
  have rel_chain: "\<forall>i. (stmp i, stmp (Suc i)) \<in> Id \<union> mRel^-1"
  proof
    fix i
    from chain(3)[of i]
    have "(stm (rs (Suc i)) (sig (Suc i)), stm (rs i) (sig i)) \<in> mRel \<or>
      stm (rs (Suc i)) (sig (Suc i)) = stm (rs i) (sig i)"
      unfolding step_cond_def by auto
    then show "(stmp i, stmp (Suc i)) \<in> Id \<union> mRel^-1"
      unfolding stmp_def by auto
  qed
  from wf_mRel have SN_mRel_inv: "SN (mRel^-1)"
    by (simp add: SN_iff_wf)
  have "\<exists>j. \<forall>i\<ge>j. (stmp i, stmp (Suc i)) \<in> Id - mRel\<inverse>"
    by (rule non_strict_ending[OF rel_chain], insert SN_mRel_inv, auto simp: SN_def)
  then obtain j where eq_steps: "\<And>i. i \<ge> j \<Longrightarrow> (stmp i, stmp (Suc i)) \<in> Id - mRel^-1"
    by auto
  have tail_narrow:
    "\<forall>i. \<exists>\<mu>. (rs (i + j), rs (Suc (i + j))) \<in> ?NSU \<mu>
      \<and> sig (i + j) = \<mu> \<circ>\<^sub>s sig (Suc (i + j))
      \<and> ((ts (i + j), ts (Suc (i + j))) \<in> ?D
        \<longrightarrow> (rs (i + j), rs (Suc (i + j))) \<in> ?NSD \<mu>)"
  proof
    fix i
    let ?n = "i + j"
    from eq_steps[of ?n] have eq_stmp: "stmp ?n = stmp (Suc ?n)"
      and not_mRel: "(stmp ?n, stmp (Suc ?n)) \<notin> mRel^-1"
      by auto
    from chain(3)[of ?n, unfolded step_cond_def]
    have branch:
      "(stm (rs (Suc ?n)) (sig (Suc ?n)), stm (rs ?n) (sig ?n)) \<in> mRel \<or>
        stm (rs (Suc ?n)) (sig (Suc ?n)) = stm (rs ?n) (sig ?n) \<and>
        (\<exists>\<mu>. narr_step ?U (rs ?n) (sig ?n) (rs (Suc ?n)) \<mu> (sig (Suc ?n)) \<and>
          ((ts ?n, ts (Suc ?n)) \<in> ?D \<longrightarrow>
            narr_step D (rs ?n) (sig ?n) (rs (Suc ?n)) \<mu> (sig (Suc ?n))))"
      by auto
    have first_false:
      "(stm (rs (Suc ?n)) (sig (Suc ?n)), stm (rs ?n) (sig ?n)) \<notin> mRel"
      using not_mRel unfolding stmp_def by auto
    from branch first_false obtain \<mu> where
      "narr_step ?U (rs ?n) (sig ?n) (rs (Suc ?n)) \<mu> (sig (Suc ?n))"
      and strict: "(ts ?n, ts (Suc ?n)) \<in> ?D \<Longrightarrow>
        narr_step D (rs ?n) (sig ?n) (rs (Suc ?n)) \<mu> (sig (Suc ?n))"
      by auto
    then show "\<exists>\<mu>. (rs (i + j), rs (Suc (i + j))) \<in> ?NSU \<mu>
      \<and> sig (i + j) = \<mu> \<circ>\<^sub>s sig (Suc (i + j))
      \<and> ((ts (i + j), ts (Suc (i + j))) \<in> ?D
        \<longrightarrow> (rs (i + j), rs (Suc (i + j))) \<in> ?NSD \<mu>)"
      unfolding narr_step_def by (intro exI[of _ \<mu>], auto)
  qed
  from choice[OF tail_narrow] obtain \<mu> where mu_tail:
    "\<And>i. (rs (i + j), rs (Suc (i + j))) \<in> ?NSU (\<mu> i)
      \<and> sig (i + j) = \<mu> i \<circ>\<^sub>s sig (Suc (i + j))
      \<and> ((ts (i + j), ts (Suc (i + j))) \<in> ?D
        \<longrightarrow> (rs (i + j), rs (Suc (i + j))) \<in> ?NSD (\<mu> i))"
    by auto
  define rs' where "rs' i = rs (i + j)" for i
  define sig' where "sig' i = sig (i + j)" for i
  have stepsU: "\<And>i. (rs' i, rs' (Suc i)) \<in> ?NSU (\<mu> i)"
    using mu_tail unfolding rs'_def by auto
  have deltaU: "\<And>i. sig' i = \<mu> i \<circ>\<^sub>s sig' (Suc i)"
    using mu_tail unfolding sig'_def by auto
  have infD_tail: "INFM i. (rs' i, rs' (Suc i)) \<in> ?NSD (\<mu> i)"
  proof -
    have "INFM i. (ts (i + j), ts (Suc (i + j))) \<in> ?D"
      unfolding INFM_nat_le
    proof
      fix m
      from raw_infD[unfolded INFM_nat_le] obtain n where n: "n \<ge> m + j"
        and step: "(ts n, ts (Suc n)) \<in> ?D" by blast
      let ?k = "n - j"
      from n have "?k \<ge> m" "n = ?k + j" by auto
      with step show "\<exists>k\<ge>m. (ts (k + j), ts (Suc (k + j))) \<in> ?D" by auto
    qed
    then show ?thesis
      unfolding INFM_nat_le using mu_tail unfolding rs'_def by metis
  qed
  from narrow_steps_to_infinite_rel_rsteps[
      where D = D and K = K and ren = ren and s = rs' and r = "rs' 0"
        and \<delta> = sig' and \<mu> = \<mu>,
      OF wf refl stepsU deltaU infD_tail]
  have "\<not> SN_on ?REL (?N\<^sup>* `` {rs' 0})" by simp
  moreover have "rs' 0 \<in> ?RFC"
    using chain(1)[of j] unfolding P_def rs'_def by auto
  ultimately show ?thesis
    unfolding right_forw_closure_def
    by (metis SN_on_def rtrancl_image_advance_rtrancl)
qed

theorem right_linear_SN_relstep_RFC:
  fixes D K :: "('f,'v::infinite)trs"
  assumes wf: "wf_trs (D \<union> K)"
    and rlin: "\<And>lr. lr \<in> D \<union> K \<Longrightarrow> linear_term (snd lr)"
  shows "SN_rel (rstep D) (rstep K) \<longleftrightarrow>
    SN_on (relto (rstep D) (rstep K)) (right_forw_closure ren (D \<union> K))"
proof
  show "SN_rel (rstep D) (rstep K) \<Longrightarrow>
    SN_on (relto (rstep D) (rstep K)) (right_forw_closure ren (D \<union> K))"
  proof -
    assume SN: "SN_rel (rstep D) (rstep K)"
    show "SN_on (relto (rstep D) (rstep K)) (right_forw_closure ren (D \<union> K))"
      by (rule SN_on_subset2[OF _ SN[unfolded SN_rel_on_def]], simp)
  qed
next
  assume "SN_on (relto (rstep D) (rstep K)) (right_forw_closure ren (D \<union> K))"
  with right_forw_closure_SN_rel_main[OF rlin wf]
  show "SN_rel (rstep D) (rstep K)" by auto
qed
*)

lemma SN_rel_from_RFC_delete_and_reverse_residual:
  fixes D K :: "('f,string)trs"
  assumes wf: "wf_trs (D \<union> K)"
    and rlin: "\<And>lr. lr \<in> D \<union> K \<Longrightarrow> linear_term (snd lr)"
    and sn_rfc: "SN_on (relto (rstep D) (rstep K)) (right_forw_closure string_rename (D \<union> K))"
    and rec: "SN_rel (rstep K) (rstep D)"
  shows "SN_rel (rstep D) (rstep K)"
proof -
  have wfD: "wf_trs D"
    using wf unfolding wf_trs_def by auto
  have rlinD: "\<And>lr. lr \<in> D \<Longrightarrow> linear_term (snd lr)"
    using rlin by auto
  have rfc_mono: "right_forw_closure string_rename D \<subseteq> right_forw_closure string_rename (D \<union> K)"
  proof -
    have ns: "narrow_step string_rename D \<subseteq> narrow_step string_rename (D \<union> K)"
      unfolding narrow_step_def narrow_step_s_def narrows_r_p_s_def by blast
    from rtrancl_mono[OF ns] show ?thesis
      unfolding right_forw_closure_def by blast
  qed
  have SN_RFC_D: "SN_on (rstep D) (right_forw_closure string_rename D)"
    by (rule SN_on_subset2[OF rfc_mono],
      rule SN_on_mono[OF sn_rfc], auto)
  have SN_D: "SN (rstep D)"
    using right_linear_SN_rstep_RFC[OF wfD rlinD, of string_rename] SN_RFC_D by simp
  show ?thesis
    unfolding SN_rel_ideriv
  proof
    assume "\<exists>as. ideriv (rstep D) (rstep K) as"
    then obtain as where id: "ideriv (rstep D) (rstep K) as" by auto
    from rec[unfolded SN_rel_ideriv] id
    have finK: "\<not> (INFM i. (as i, as (Suc i)) \<in> rstep K)"
      unfolding ideriv_def by auto
    from finK[unfolded INFM_nat] obtain j where noK:
      "\<And>i. j < i \<Longrightarrow> (as i, as (Suc i)) \<notin> rstep K"
      by auto
    let ?bs = "shift as (Suc j)"
    have "ideriv (rstep D) {} ?bs"
      unfolding ideriv_def
    proof (intro conjI allI)
      fix i
      from id have step: "(as (i + Suc j), as (Suc (i + Suc j))) \<in> rstep D \<union> rstep K"
        unfolding ideriv_def by auto
      moreover have "(as (i + Suc j), as (Suc (i + Suc j))) \<notin> rstep K"
        by (rule noK, auto)
      ultimately show "(?bs i, ?bs (Suc i)) \<in> rstep D \<union> {}"
        by auto
    next
      from id have infD: "INFM i. (as i, as (Suc i)) \<in> rstep D"
        unfolding ideriv_def by auto
      show "INFM i. (?bs i, ?bs (Suc i)) \<in> rstep D"
        unfolding INFM_nat
      proof
        fix m
        from infD[unfolded INFM_nat] obtain n where n: "n > m + Suc j"
          and D: "(as n, as (Suc n)) \<in> rstep D"
          by auto
        show "\<exists>n>m. (?bs n, ?bs (Suc n)) \<in> rstep D"
          by (rule exI[of _ "n - Suc j"], insert n D, auto)
      qed
    qed
    moreover from SN_D have "SN_rel (rstep D) {}"
      by simp
    ultimately show False
      unfolding SN_rel_ideriv by blast
  qed
qed

lemma rfc_relative_bounds_impl_semantic_on:
  fixes R S :: "('f,string)rules"
    and TA :: "('q,'f \<times> nat)ta"
    and rel :: "'q rel"
    and A :: "('f,string)terms"
  assumes choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel (cover_bound c Matchbounds.match Strict_TRS (set R))"
    and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))"
    and coh: "state_coherent TA rel"
    and tab: "ta_bounded TA c"
    and qfin: "\<exists>q\<in>qfin. q \<in> ta_rhs_states TA"
    and qfin_final: "qfin \<subseteq> ta_final TA"
    and inf: "infinite (UNIV :: 'f set)"
    and wf: "wf_trs (set R \<union> set S)"
    and nondup: "\<And>l r. (l,r) \<in> set R \<union> set S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
    and wkc: "weak_kind_condition c c_opt (set R)"
    and acc: "\<And>t q. t \<in> A \<Longrightarrow> q \<in> qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  shows "SN_on (relto (rstep (set R)) (rstep (set S))) A"
proof -
  let ?RR = "set R"
  let ?SS = "set S"
  have empty_contain: "ta_contains ((\<lambda>(f,n). (lift 0 f,n)) ` {})
      ((\<lambda>(f,n). (lift 0 f,n)) ` {}) TA qfin"
    unfolding ta_contains_def ta_contains_aux_def by simp
  from create_constant_in_ta_two[
      where G = "{}" and H = "{}",
      OF fin coh finite.emptyI finite.emptyI empty_contain qfin_final qfin tab inf choice compat compat2]
  obtain q const F F' TA' where q_in: "q \<in> qfin"
    and comp: "state_compatible TA' rel (cover Matchbounds.match Strict_TRS ?RR)"
    and comp2: "state_compatible TA' rel (cover Matchbounds.match (Weak_TRS c_opt) ?SS)"
    and coh': "state_coherent TA' rel"
    and choice': "left_linear_trs (?RR \<union> ?SS) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    and tab': "ta_bounded TA' c"
    and TA': "TA' = \<lparr> ta_final = ta_final TA,
      ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
    by blast
  have finTA': "finite (ta_rules TA')" unfolding TA' using fin by simp
  let ?\<sigma> = "\<lambda>_. Fun const []"
  let ?L = "((\<lambda>t :: ('f,string)term. t \<cdot> ?\<sigma>) ` A :: ('f,string)terms)"
  have const_rule: "((const,0) [] \<rightarrow> q) \<in> ta_rules TA'"
    unfolding TA' by simp
  have const_res: "q \<in> ta_res TA' (Fun (const,0) [])"
    unfolding ta_res.simps
    by (rule CollectI, rule exI[of _ q], rule exI[of _ q], rule exI[of _ "[]"],
      insert const_rule, simp)
  have lift_L: "lift_term 0 ` ?L \<subseteq> (ta_lang TA' :: ('f \<times> nat,string)terms)"
  proof
    fix lt :: "('f \<times> nat,string)term"
    assume "lt \<in> lift_term 0 ` ?L"
    then obtain t where t: "t \<in> A" and lt: "lt = lift_term 0 (t \<cdot> ?\<sigma>)"
      by blast
    from acc[OF t q_in] obtain qf where qf: "qf \<in> ta_final TA"
      and qres: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      by auto
    have qres': "qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    proof -
      have eps_sub: "ta_eps TA \<subseteq> ta_eps TA'"
        unfolding TA' by simp
      have rules_sub: "ta_rules TA \<subseteq> ta_rules TA'"
        unfolding TA' by auto
      from eps_sub rules_sub have "ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))
        \<subseteq> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
        by (rule ta_res_mono')
      with qres show ?thesis ..
    qed
    have qvars: "\<And>x. x \<in> vars_term (lift_term 0 t) \<Longrightarrow>
        q \<in> ta_res TA' (Fun (const,0) [])"
      using const_res .
    have subst_res: "qf \<in> ta_res TA'
        (lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) []))"
      by (rule ta_res_subst[OF qvars qres'])
    have ground_inst: "ground (lift_term 0 (t \<cdot> ?\<sigma>))"
      by (induct t) auto
    have subst_id: "adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)) =
        lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) [])"
      by (simp add: adapt_vars_lift_term_subst)
    have qres_inst: "qf \<in> ta_res TA'
        (adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)))"
      using subst_res unfolding subst_id .
    show "lt \<in> (ta_lang TA' :: ('f \<times> nat,string)terms)"
    proof (unfold lt, rule ta_langI2[OF ground_inst _ qres_inst])
      show "qf \<in> ta_final TA'" using qf unfolding TA' by simp
    qed
  qed
  let ?F = "unlift_sig ` ta_syms TA'"
  have finF: "finite ?F"
    by (rule finite_imageI[OF finite_ta_syms[OF finTA']])
  have funas_L: "\<Union> (funas_term ` ?L) \<subseteq> ?F"
    apply (rule Union_least)
    apply (erule imageE[where A="?L"])
    apply hypsubst
    apply (rule_tac u="x :: ('f,string)term" in funas_lift_term_ta_lang_subset)
    apply (rule subsetD[OF lift_L])
    apply (rule imageI)
    apply assumption
    done
  have comp_union: "state_compatible TA' rel
      (cover Matchbounds.match Strict_TRS ?RR \<union> cover Matchbounds.match (Weak_TRS c_opt) ?SS)"
    using comp comp2 unfolding state_compatible_union by blast
  have choice_cover: "left_linear_trs
      (cover Matchbounds.match Strict_TRS ?RR \<union> cover Matchbounds.match (Weak_TRS c_opt) ?SS)
      \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    using choice' cover_left_linear unfolding left_linear_trs_union by blast
  have varcond: "\<And>l r. (l,r) \<in>
      cover Matchbounds.match Strict_TRS ?RR \<union> cover Matchbounds.match (Weak_TRS c_opt) ?SS
      \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    using wf[unfolded wf_trs_def] cover_var_condition[of _ _ _ Matchbounds.match]
    by blast
  have bounded: "match_raise_rel_bounded c c_opt ?RR ?SS ?L"
  proof -
    have "raise_step_bounded c
        (cover Matchbounds.match Strict_TRS ?RR \<union> cover Matchbounds.match (Weak_TRS c_opt) ?SS) ?L"
      by (rule Matchbounds_Impl.raise_step_boundedI[
          where TA = TA' and rel = rel and L = ?L and c = c,
          OF choice_cover finTA' comp_union coh' lift_L tab' varcond])
    then show ?thesis
      unfolding match_raise_rel_bounded_def .
  qed
  from match_raise_bounded_linear_complexity_rel_main[
      OF wf _ funas_L nondup wkc bounded]
  have lin: "\<exists>d. \<forall>n s t. s \<in> ?L \<longrightarrow>
      (s, t) \<in> (relto (rstep ?RR) (rstep ?SS)) ^^ n \<longrightarrow>
      n \<le> term_size s * d"
    by auto
  have SN_L: "SN_on (relto (rstep ?RR) (rstep ?SS)) ?L"
    by (rule linear_rel_bound_SN_on[OF lin])
  show ?thesis
  proof
    fix f
    assume f0: "f 0 \<in> A"
      and steps: "\<forall>i. (f i, f (Suc i)) \<in> relto (rstep ?RR) (rstep ?SS)"
    let ?g = "\<lambda>i. f i \<cdot> ?\<sigma>"
    have g0: "?g 0 \<in> ?L"
      using f0 by blast
    have gsteps: "\<forall>i. (?g i, ?g (Suc i)) \<in> relto (rstep ?RR) (rstep ?SS)"
    proof
      fix i
      from steps have "(f i, f (Suc i)) \<in> relto (rstep ?RR) (rstep ?SS)"
        by auto
      then obtain u v where fu: "(f i, u) \<in> (rstep ?SS)\<^sup>*"
        and uv: "(u, v) \<in> rstep ?RR"
        and vf: "(v, f (Suc i)) \<in> (rstep ?SS)\<^sup>*"
        by auto
      have fu': "(f i \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> (rstep ?SS)\<^sup>*"
        by (rule subst.closedD[OF subst.closed_rtrancl[OF subst_closed_rstep] fu])
      have uv': "(u \<cdot> ?\<sigma>, v \<cdot> ?\<sigma>) \<in> rstep ?RR"
        by (rule subst.closedD[OF subst_closed_rstep uv])
      have vf': "(v \<cdot> ?\<sigma>, f (Suc i) \<cdot> ?\<sigma>) \<in> (rstep ?SS)\<^sup>*"
        by (rule subst.closedD[OF subst.closed_rtrancl[OF subst_closed_rstep] vf])
      from fu' uv' vf' show "(?g i, ?g (Suc i)) \<in> relto (rstep ?RR) (rstep ?SS)"
        by auto
    qed
    from SN_L g0 gsteps show False
      unfolding SN_on_def by auto
  qed
qed

lemma rfc_relative_bounds_impl_semantic:
  fixes R S Rall :: "('f,string)rules"
    and TA :: "('q,'f \<times> nat)ta"
    and rel :: "'q rel"
  assumes choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel (cover_bound c Matchbounds.match Strict_TRS (set R))"
    and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))"
    and coh: "state_coherent TA rel"
    and tab: "ta_bounded TA c"
    and qfin: "\<exists>q\<in>qfin. q \<in> ta_rhs_states TA"
    and qfin_final: "qfin \<subseteq> ta_final TA"
    and inf: "infinite (UNIV :: 'f set)"
    and wf: "wf_trs (set R \<union> set S)"
    and nondup: "\<And>l r. (l,r) \<in> set R \<union> set S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
    and wkc: "weak_kind_condition c c_opt (set R)"
    and rfc_acc: "\<And>t q. t \<in> rfc_forward_closure Rall \<Longrightarrow> q \<in> qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  shows "SN_on (relto (rstep (set R)) (rstep (set S))) (rfc_forward_closure Rall)"
  by (rule rfc_relative_bounds_impl_semantic_on[OF choice fin compat compat2 coh tab qfin
        qfin_final inf wf nondup wkc rfc_acc])

lemma rfc_relative_bounds_impl_semantic_exists:
  fixes R S :: "('f,string)rules"
    and TA :: "('q,'f \<times> nat)ta"
    and rel :: "'q rel"
    and A :: "('f,string)terms"
  assumes choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel (cover_bound c Matchbounds.match Strict_TRS (set R))"
    and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))"
    and coh: "state_coherent TA rel"
    and tab: "ta_bounded TA c"
    and inf: "infinite (UNIV :: 'f set)"
    and wf: "wf_trs (set R \<union> set S)"
    and nondup: "\<And>l r. (l,r) \<in> set R \<union> set S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
    and wkc: "weak_kind_condition c c_opt (set R)"
    and acc: "\<And>t. t \<in> A \<Longrightarrow> \<exists>q. q \<in> ta_rhs_states TA \<and> q \<in> ta_final TA \<and>
      (\<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
  shows "SN_on (relto (rstep (set R)) (rstep (set S))) A"
proof
  fix f
  assume f0: "f 0 \<in> A"
    and steps: "\<forall>i. (f i, f (Suc i)) \<in> relto (rstep (set R)) (rstep (set S))"
  from acc[OF f0] obtain q qf where q_rhs: "q \<in> ta_rhs_states TA"
    and q_final: "q \<in> ta_final TA"
    and qf_final: "qf \<in> ta_final TA"
    and qf_res: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 (f 0)))"
    by blast
  have singleton_SN: "SN_on (relto (rstep (set R)) (rstep (set S))) {f 0}"
  proof (rule rfc_relative_bounds_impl_semantic_on[
      where qfin = "{q}" and A = "{f 0}",
      OF choice fin compat compat2 coh tab])
    show "\<exists>q'\<in>{q}. q' \<in> ta_rhs_states TA"
      using q_rhs by blast
    show "{q} \<subseteq> ta_final TA"
      using q_final by blast
    show "infinite (UNIV :: 'f set)"
      by (rule inf)
    show "wf_trs (set R \<union> set S)"
      by (rule wf)
    show "\<And>l r. (l, r) \<in> set R \<union> set S \<Longrightarrow> vars_term_ms r \<subseteq># vars_term_ms l"
      by (rule nondup)
    show "weak_kind_condition c c_opt (set R)"
      by (rule wkc)
    show "\<And>t q'. t \<in> {f 0} \<Longrightarrow> q' \<in> {q} \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q') (lift_term 0 t))"
      using qf_final qf_res by auto
  qed
  from singleton_SN steps show False
    unfolding SN_on_def by auto
qed

lemma rfc_bounds_impl_semantic:
  fixes R S :: "('f,string)rules"
    and TA :: "('q,'f \<times> nat)ta"
    and rel :: "'q rel"
  assumes choice: "left_linear_trs (set (R @ S)) \<or> ta_det TA \<and> state_raise_consistent TA rel"
    and fin: "finite (ta_rules TA)"
    and compat: "state_compatible TA rel (cover_bound c e Strict_TRS (set R))"
    and compat2: "state_compatible TA rel (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set S))"
    and coh: "state_coherent TA rel"
    and tab: "ta_bounded TA c"
    and qfin: "\<exists>q\<in>qfin. q \<in> ta_rhs_states TA"
    and qfin_final: "qfin \<subseteq> ta_final TA"
    and inf: "infinite (UNIV :: 'f set)"
    and wf: "wf_trs (set R \<union> set S)"
    and SN: "locally_terminating (cover e Strict_TRS (set R) \<union> Matchbounds.raise)"
    and rhs_lin: "\<And>lr. lr \<in> set R \<Longrightarrow> linear_term (snd lr)"
    and rfc_acc: "\<And>t q. t \<in> rfc_forward_closure R \<Longrightarrow> q \<in> qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final TA. qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  shows "SN (rstep (set R))"
proof -
  let ?RR = "set R"
  let ?RFC = "rfc_forward_closure R"
  from wf have wf_R: "wf_trs ?RR"
    unfolding wf_trs_def by blast
  from wf[unfolded wf_trs_def] have varcond: "\<And>l r. (l,r) \<in> ?RR \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    by blast
  let ?lz = "\<lambda>(f,n). (lift 0 f,n)"
  have empty_contain: "ta_contains (?lz ` {}) (?lz ` {}) TA qfin"
    unfolding ta_contains_def ta_contains_aux_def by simp
  from create_constant_in_ta_two[
    where G = "{}" and H = "{}",
    OF fin coh finite.emptyI finite.emptyI empty_contain qfin_final qfin tab inf choice compat compat2]
  obtain q const F F' TA' where q_in: "q \<in> qfin"
    and comp: "state_compatible TA' rel (cover e Strict_TRS ?RR)"
    and coh': "state_coherent TA' rel"
    and choice': "left_linear_trs (?RR \<union> set S) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    and tab': "ta_bounded TA' c"
    and TA': "TA' = \<lparr> ta_final = ta_final TA,
      ta_rules = insert ((const,0) [] \<rightarrow> q) (ta_rules TA), ta_eps = ta_eps TA \<rparr>"
    by blast
  have choice_R: "left_linear_trs (cover e Strict_TRS ?RR) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
    using choice' cover_left_linear unfolding left_linear_trs_union by blast
  have finTA': "finite (ta_rules TA')" unfolding TA' using fin by simp
  let ?\<sigma> = "\<lambda>_. Fun const []"
  let ?L = "((\<lambda>t :: ('f,string)term. t \<cdot> ?\<sigma>) ` ?RFC :: ('f,string)terms)"
  have lift_L: "lift_term 0 ` ?L \<subseteq> (ta_lang TA' :: ('f \<times> nat,string)terms)"
  proof
    fix lt :: "('f \<times> nat,string)term"
    assume "lt \<in> lift_term 0 ` ?L"
    then obtain t where t: "t \<in> ?RFC" and lt: "lt = lift_term 0 (t \<cdot> ?\<sigma>)"
      by blast
    have const_rule: "((const,0) [] \<rightarrow> q) \<in> ta_rules TA'"
      unfolding TA' by simp
    have const_res: "q \<in> ta_res TA' (Fun (const,0) [])"
      unfolding ta_res.simps
      by (rule CollectI, rule exI[of _ q], rule exI[of _ q], rule exI[of _ "[]"],
        insert const_rule, simp)
    from rfc_acc[OF t q_in] obtain qf where qf: "qf \<in> ta_final TA"
      and qres: "qf \<in> ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      by auto
    have qres': "qf \<in> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    proof -
      have eps_sub: "ta_eps TA \<subseteq> ta_eps TA'"
        unfolding TA' by simp
      have rules_sub: "ta_rules TA \<subseteq> ta_rules TA'"
        unfolding TA' by (rule subsetI, simp)
      from eps_sub rules_sub have "ta_res TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))
        \<subseteq> ta_res TA' (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
        by (rule ta_res_mono')
      with qres show ?thesis ..
    qed
    have qvars: "\<And>x. x \<in> vars_term (lift_term 0 t) \<Longrightarrow>
        q \<in> ta_res TA' (Fun (const,0) [])"
      using const_res .
    have subst_res: "qf \<in> ta_res TA'
        (lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) []))"
      by (rule ta_res_subst[OF qvars qres'])
    have ground_inst: "ground (lift_term 0 (t \<cdot> ?\<sigma>))"
      by (induct t) auto
    have subst_id: "adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)) =
        lift_term 0 t \<cdot> (\<lambda>x. Fun (const,0) [])"
      by (simp add: adapt_vars_lift_term_subst)
    have qres_inst: "qf \<in> ta_res TA' (adapt_vars (lift_term 0 (t \<cdot> ?\<sigma>)))"
      using subst_res unfolding subst_id .
    show "lt \<in> (ta_lang TA' :: ('f \<times> nat,string)terms)"
    proof (unfold lt, rule ta_langI2[OF ground_inst _ qres_inst])
      show "qf \<in> ta_final TA'" using qf unfolding TA' by simp
    qed
  qed
  let ?F = "unlift_sig ` ta_syms TA'"
  have finF: "finite ?F"
    by (rule finite_imageI[OF finite_ta_syms[OF finTA']])
  have funas_L: "\<Union> (funas_term ` ?L) \<subseteq> ?F"
    apply (rule Union_least)
    apply (erule imageE[where A="?L"])
    apply hypsubst
    apply (rule_tac u="x :: ('f,string)term" in funas_lift_term_ta_lang_subset)
    apply (rule subsetD[OF lift_L])
    apply (rule imageI)
    apply assumption
    done
  have SN_L: "SN_on (rstep ?RR) ?L"
  proof (rule Matchbounds_Impl.e_bounds[
      where TA = TA' and rel = rel and c = c and R = "cover e Strict_TRS ?RR"
        and L = ?L and F = ?F and RR = ?RR and e = e])
    show "left_linear_trs (cover e Strict_TRS ?RR) \<or> ta_det TA' \<and> state_raise_consistent TA' rel"
      by (rule choice_R)
    show "finite (ta_rules TA')" by (rule finTA')
    show "state_compatible TA' rel (cover e Strict_TRS ?RR)" by (rule comp)
    show "state_coherent TA' rel" by (rule coh')
    show "lift_term 0 ` ?L \<subseteq> (ta_lang TA' :: ('f \<times> nat,string)terms)"
      using lift_L .
    show "ta_bounded TA' c" by (rule tab')
    show "locally_terminating (cover e Strict_TRS ?RR \<union> Matchbounds.raise)" by (rule SN)
    show "finite ?F" by (rule finF)
    show "finite ?RR" by simp
    show "cover e Strict_TRS ?RR = cover e Strict_TRS ?RR" by simp
    show "\<And>l r. (l, r) \<in> ?RR \<Longrightarrow> vars_term r \<subseteq> vars_term l" by (rule varcond)
    show "\<Union> (funas_term ` ?L) \<subseteq> ?F" by (rule funas_L)
  qed
  have SN_RFC: "SN_on (rstep ?RR) ?RFC"
  proof
    fix f
    assume f0: "f 0 \<in> ?RFC" and steps: "\<forall>i. (f i, f (Suc i)) \<in> rstep ?RR"
    have inst: "f 0 \<cdot> ?\<sigma> \<in> ?L"
      using f0 by blast
    have singleton_sub: "{f 0 \<cdot> ?\<sigma>} \<subseteq> ?L"
      using inst by auto
    have "SN_on (rstep ?RR) {f 0 \<cdot> ?\<sigma>}"
      by (rule SN_on_subset2[OF singleton_sub SN_L])
    from SNinstance_imp_SN[OF this] steps
    show False unfolding SN_defs by auto
  qed
  have SN_right: "SN_on (rstep ?RR) (right_forw_closure string_rename ?RR)"
    using SN_RFC unfolding rfc_forward_closure_eq .
  from right_linear_SN_rstep_RFC[OF wf_R rhs_lin, of string_rename] SN_right
  show ?thesis by simp
qed

lemma rfc_automaton_closed_relative_bounds_SN_on:
  fixes info :: "('f::{linorder,showl,compare_order}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I"
    and ok: "isOK (rfc_automaton_closed_relative_bounds_tt I info initial_terms Rdelete tp)"
    and inf: "infinite (UNIV :: 'f set)"
  shows "SN_on
    (relto (rstep (set Rdelete)) (rstep (set (ceta_list_diff (tp_ops.R I tp) Rdelete))))
    (rfc_forward_closure (tp_ops.R I tp))"
proof -
  interpret tp_spec I by fact
  obtain bi ren where ren: "get_integer_bounds_info info = (bi, ren)"
    by (cases "get_integer_bounds_info info", auto)
  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, auto)
  have info_eq: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel, ren)"
    using ren info' by simp
  let ?Rstrict = "R tp"
  let ?Rkeep = "ceta_list_diff ?Rstrict Rdelete"
  let ?states = "remdups (states_of_tree_automata_dup preTA)"
  from ok[unfolded rfc_automaton_closed_relative_bounds_tt_def ren info' Let_def]
  obtain TA where TA: "generate_ta_cond preTA rel = return TA"
    and okb: "isOK (check_bounds_generic_rfc_relative info Rdelete ?Rkeep)"
    by auto
  from generate_ta_cond[OF TA] have inv: "ta_inv TA (rel_checker rel) (relation_of rel)"
    and TA_gen: "TA = generate_ta preTA" by auto
  let ?TA = "(ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
  from ok[unfolded rfc_automaton_closed_relative_bounds_tt_def ren info' Let_def]
  have bt: "boundstype info = Match"
    and rhs_lin_list: "list_all (\<lambda>(l, r). linear_term r) ?Rstrict"
    and initial_covers: "rfc_initial_covers ?Rstrict initial_terms"
    and initial_acc_proj: "rfc_initial_accepted_with_tail_states_impl TYPE('f)
      (projr (generate_ta_cond preTA rel)) ?states initial_terms"
    and closed_proj: "rfc_automaton_closed_impl (projr (generate_ta_cond preTA rel)) ?states ?Rstrict"
    and suffix_total_proj: "rfc_lhs_suffix_total_impl (projr (generate_ta_cond preTA rel)) ?states ?Rstrict"
    and no_top_proj: "rfc_no_top_redex_impl
      (projr (generate_ta_cond preTA rel)) ?states c Rdelete"
    by (auto simp: Q_empty_sound)
  have initial_acc_impl: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TA ?states initial_terms"
    using initial_acc_proj TA by simp
  have closed: "rfc_automaton_closed_impl TA ?states ?Rstrict"
    using closed_proj TA by simp
  have suffix_total: "rfc_lhs_suffix_total_impl TA ?states ?Rstrict"
    using suffix_total_proj TA by simp
  have no_top: "rfc_no_top_redex_impl TA ?states c Rdelete"
    using no_top_proj TA by simp
  from check_bounds_generic_rfc_relative_exact[
      where R = "(Rdelete :: ('f,string)rules)"
        and S = "?Rkeep"
        and info = info
        and type = type
        and c = c
        and qfin = qfin
        and preTA = preTA
        and rel_info = rel
        and ren = ren,
      OF okb info_eq]
  obtain b_rel c_opt where bounds:
    "b_rel = relation_of rel
    \<and> left_linear_trs (set (Rdelete @ ?Rkeep))
    \<and> finite (ta_rules ?TA)
    \<and> state_compatible ?TA b_rel
      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})
    \<and> state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))
    \<and> state_coherent ?TA b_rel
    \<and> ta_bounded ?TA c
    \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA)
    \<and> set qfin \<subseteq> ta_final ?TA
    \<and> wf_trs (set Rdelete \<union> set ?Rkeep)
    \<and> isOK (bounds_condition (boundstype info) (Rdelete @ ?Rkeep))
    \<and> weak_kind_condition c c_opt (set Rdelete)"
    by auto
  from bounds have b_rel: "b_rel = relation_of rel"
    and left_linear_b: "left_linear_trs (set (Rdelete @ ?Rkeep))"
    and fin_b: "finite (ta_rules ?TA)"
    and below_raw: "state_compatible ?TA b_rel
      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
    and compat_keep_b: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))"
    and coh_b: "state_coherent ?TA b_rel"
    and tab_b: "ta_bounded ?TA c"
    and qfin_b: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA"
    and qfin_final_b: "set qfin \<subseteq> ta_final ?TA"
    and wf_b: "wf_trs (set Rdelete \<union> set ?Rkeep)"
    and cond_raw: "isOK (bounds_condition (boundstype info) (Rdelete @ ?Rkeep))"
    and wkc_b: "weak_kind_condition c c_opt (set Rdelete)"
    by auto
  have below: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
    using below_raw bt by simp
  have state_cover: "ta_states ?TA \<subseteq> set ?states"
    using ta_states_generate_ta_states_of_tree_automata_dup by auto
  have state_cover_impl: "ta_states (ta_of TA) \<subseteq> set ?states"
    using state_cover unfolding TA_gen .
  have compat_delete: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
  proof -
    have below_impl: "state_compatible (ta_of TA) b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
      using below unfolding TA_gen .
    have "state_compatible (ta_of TA) (relation_of rel)
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
      by (rule rfc_no_top_redex_full_strict_compat[
          OF inv state_cover_impl _ no_top])
        (use below_impl b_rel in simp)
    then show ?thesis
      unfolding TA_gen using b_rel by simp
  qed
  have compat_keep: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))"
    by (rule compat_keep_b)
  have cond: "isOK (bounds_condition Match (Rdelete @ ?Rkeep))"
    using cond_raw bt by simp
  have nondup: "\<And>l r. (l, r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l"
    using cond by (auto simp: isOK_check_allm)
  have initial_acc_all: "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> ta_states ?TA \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  proof -
    fix t q
    assume t: "t \<in> set initial_terms" and q: "q \<in> ta_states ?TA"
    have q_list: "q \<in> set ?states"
      using state_cover q by auto
    from rfc_initial_accepted_with_tail_states_impl[OF inv initial_acc_impl t q_list]
    show "\<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      unfolding TA_gen .
  qed
  have initial_acc_all_impl:
    "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> ta_states (ta_of TA) \<Longrightarrow>
      \<exists>qf\<in>ta_final (ta_of TA).
        qf \<in> ta_res (ta_of TA) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
    using initial_acc_all unfolding TA_gen .
  have rfc_acc: "\<And>t q. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  proof -
    fix t q
    assume t: "t \<in> rfc_forward_closure ?Rstrict" and q: "q \<in> set qfin"
    have q_state: "q \<in> ta_states ?TA"
      using q qfin_final_b unfolding ta_states_def by auto
    have q_state_impl: "q \<in> ta_states (ta_of TA)"
      using q_state unfolding TA_gen .
    from rfc_automaton_closed_forward_closure_accepted[
      OF inv state_cover_impl closed suffix_total initial_covers initial_acc_all_impl t q_state_impl]
    show "\<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      unfolding TA_gen .
  qed
  show ?thesis
  proof (rule rfc_relative_bounds_impl_semantic[
      where R = "Rdelete" and S = "?Rkeep" and Rall = "?Rstrict"
        and TA = ?TA and rel = b_rel and c = c and c_opt = c_opt
        and qfin = "set qfin"])
    show "left_linear_trs (set (Rdelete @ ?Rkeep)) \<or>
      ta_det ?TA \<and> state_raise_consistent ?TA b_rel"
      using left_linear_b by blast
    show "finite (ta_rules ?TA)"
      by (rule fin_b)
    show "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
      by (rule compat_delete)
    show "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))"
      by (rule compat_keep)
    show "state_coherent ?TA b_rel"
      by (rule coh_b)
    show "ta_bounded ?TA c"
      by (rule tab_b)
    show "\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA"
      by (rule qfin_b)
    show "set qfin \<subseteq> ta_final ?TA"
      by (rule qfin_final_b)
    show "infinite (UNIV :: 'f set)"
      by (rule inf)
    show "wf_trs (set Rdelete \<union> set ?Rkeep)"
      by (rule wf_b)
    show "\<And>l r. (l, r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l"
      by (rule nondup)
    show "weak_kind_condition c c_opt (set Rdelete)"
      by (rule wkc_b)
    show "\<And>t q. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      by (rule rfc_acc)
  qed
qed

lemma rfc_matchbox_relative_bounds_SN_on:
  fixes info :: "('f::{linorder,showl,compare_order}, 'q::{compare_order,showl}) bounds_info"
  assumes "tp_spec I"
    and ok: "isOK (rfc_matchbox_relative_bounds_tt I info initial_terms Rdelete tp)"
    and inf: "infinite (UNIV :: 'f set)"
  shows "SN_on
    (relto (rstep (set Rdelete)) (rstep (set (ceta_list_diff (tp_ops.R I tp) Rdelete))))
    (rfc_forward_closure (tp_ops.R I tp))"
proof -
  interpret tp_spec I by fact
  let ?pinfo = "info"
  obtain bi ren where ren: "get_integer_bounds_info ?pinfo = (bi, ren)"
    by (cases "get_integer_bounds_info ?pinfo", auto)
  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, auto)
  have info_eq: "get_integer_bounds_info ?pinfo = (Bounds_Info type c qfin preTA rel, ren)"
    using ren info' by simp
  let ?Rstrict = "R tp"
  let ?Rkeep = "ceta_list_diff ?Rstrict Rdelete"
  let ?states = "remdups (states_of_tree_automata_dup preTA)"
  from ok[unfolded rfc_matchbox_relative_bounds_tt_def ren info' Let_def]
  obtain TA where TA: "generate_ta_cond preTA rel = return TA"
    and okb: "isOK (check_bounds_generic_rfc_relative ?pinfo Rdelete ?Rkeep)"
    by auto
  from generate_ta_cond[OF TA] have inv: "ta_inv TA (rel_checker rel) (relation_of rel)"
    and TA_gen: "TA = generate_ta preTA" by auto
  let ?TA = "(ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
  from ok[unfolded rfc_matchbox_relative_bounds_tt_def ren info' Let_def]
  have bt: "boundstype info = Match"
    and rhs_lin_list: "list_all (\<lambda>(l, r). linear_term r) ?Rstrict"
    and initial_covers: "rfc_initial_covers ?Rstrict initial_terms"
    and qfin_rhs_proj: "list_all
      (\<lambda>q. rs.memb q (ta_rhs_states_set (projr (generate_ta_cond preTA rel)))) qfin"
    and initial_acc_proj: "rfc_initial_paired_accepted_impl TYPE('f)
      (projr (generate_ta_cond preTA rel)) qfin initial_terms"
    and closed_proj: "rfc_matchbox_closed_indexed_impl
      (projr (generate_ta_cond preTA rel)) rel ?states ?Rstrict"
    and ext_right_proj: "rfc_matchbox_ext_right_indexed_impl
      (projr (generate_ta_cond preTA rel)) rel qfin ?states ?Rstrict"
    and no_top_fast_proj: "rfc_no_top_redex_indexed_impl
      (projr (generate_ta_cond preTA rel)) ?states c Rdelete"
    by (auto simp: Q_empty_sound)
  have initial_acc_impl: "rfc_initial_paired_accepted_impl TYPE('f) TA qfin initial_terms"
    using initial_acc_proj TA by simp
  have closed: "rfc_matchbox_closed_impl TA rel ?states ?Rstrict"
    using closed_proj TA
    by (simp add: rfc_matchbox_closed_indexed_impl_eq)
  have ext_right: "rfc_matchbox_ext_right_impl TA rel qfin ?states ?Rstrict"
    using ext_right_proj TA
    by (simp add: rfc_matchbox_ext_right_indexed_impl_eq)
  have no_top_fast: "rfc_no_top_redex_fast_impl TA ?states c Rdelete"
    using no_top_fast_proj TA
    by (simp add: rfc_no_top_redex_indexed_impl_eq)
  have no_top: "rfc_no_top_redex_impl TA ?states c Rdelete"
    by (rule rfc_no_top_redex_fast_impl_imp[OF no_top_fast])
  from check_bounds_generic_rfc_relative_exact[
      where R = "(Rdelete :: ('f,string)rules)"
        and S = "?Rkeep"
        and info = "?pinfo"
        and type = type
        and c = c
        and qfin = qfin
        and preTA = preTA
        and rel_info = rel
        and ren = ren,
      OF okb info_eq]
  obtain b_rel c_opt where bounds:
    "b_rel = relation_of rel
    \<and> left_linear_trs (set (Rdelete @ ?Rkeep))
    \<and> finite (ta_rules ?TA)
    \<and> state_compatible ?TA b_rel
      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})
    \<and> state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))
    \<and> state_coherent ?TA b_rel
    \<and> ta_bounded ?TA c
    \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA)
    \<and> set qfin \<subseteq> ta_final ?TA
    \<and> wf_trs (set Rdelete \<union> set ?Rkeep)
    \<and> isOK (bounds_condition (boundstype info) (Rdelete @ ?Rkeep))
    \<and> weak_kind_condition c c_opt (set Rdelete)"
    by auto
  from bounds have b_rel: "b_rel = relation_of rel"
    and left_linear_b: "left_linear_trs (set (Rdelete @ ?Rkeep))"
    and fin_b: "finite (ta_rules ?TA)"
    and below_raw: "state_compatible ?TA b_rel
      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
    and compat_keep_b: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))"
    and coh_b: "state_coherent ?TA b_rel"
    and tab_b: "ta_bounded ?TA c"
    and qfin_b: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA"
    and qfin_final_b: "set qfin \<subseteq> ta_final ?TA"
    and wf_b: "wf_trs (set Rdelete \<union> set ?Rkeep)"
    and cond_raw: "isOK (bounds_condition (boundstype info) (Rdelete @ ?Rkeep))"
    and wkc_b: "weak_kind_condition c c_opt (set Rdelete)"
    by auto
  have below: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
    using below_raw bt by simp
  have state_cover: "ta_states ?TA \<subseteq> set ?states"
    using ta_states_generate_ta_states_of_tree_automata_dup by auto
  have state_cover_impl: "ta_states (ta_of TA) \<subseteq> set ?states"
    using state_cover unfolding TA_gen .
  have coh_impl: "state_coherent (ta_of TA) (relation_of rel)"
    using coh_b b_rel unfolding TA_gen by simp
  have compat_delete: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
  proof -
    have below_impl: "state_compatible (ta_of TA) b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete) \<inter>
        {(l,r). \<not> rfc_lifted_lhs_top_impl c l})"
      using below unfolding TA_gen .
    have "state_compatible (ta_of TA) (relation_of rel)
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
      by (rule rfc_no_top_redex_full_strict_compat[
          OF inv state_cover_impl _ no_top])
        (use below_impl b_rel in simp)
    then show ?thesis
      unfolding TA_gen using b_rel by simp
  qed
  have compat_keep: "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))"
    by (rule compat_keep_b)
  have cond: "isOK (bounds_condition Match (Rdelete @ ?Rkeep))"
    using cond_raw bt by simp
  have nondup: "\<And>l r. (l, r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l"
    using cond by (auto simp: isOK_check_allm)
  have qfin_rhs_impl: "set qfin \<subseteq> ta_rhs_states (ta_of TA)"
    using qfin_rhs_proj TA ta_inv.ta_rhs_states_set[OF inv]
    by (auto simp: list_all_iff rs.correct)
  have rfc_acc: "\<And>t. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow>
      \<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
        (\<exists>qf\<in>ta_final ?TA.
          qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
  proof -
    fix t
    assume t: "t \<in> rfc_forward_closure ?Rstrict"
    from rfc_matchbox_paired_forward_closure_accepted[
      OF inv state_cover_impl coh_impl closed ext_right initial_covers initial_acc_impl
        _ t]
    obtain q qf where q: "q \<in> set qfin"
      and qf: "qf \<in> ta_final (ta_of TA)"
      and acc: "qf \<in> ta_res (ta_of TA)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      using qfin_final_b unfolding TA_gen by blast
    have q_rhs: "q \<in> ta_rhs_states (ta_of TA)"
      using qfin_rhs_impl q by blast
    have q_final: "q \<in> ta_final (ta_of TA)"
      using qfin_final_b q unfolding TA_gen by blast
    show "\<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
        (\<exists>qf\<in>ta_final ?TA.
          qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
      using q_rhs q_final qf acc unfolding TA_gen by blast
  qed
  show ?thesis
  proof (rule rfc_relative_bounds_impl_semantic_exists[
      where R = "Rdelete" and S = "?Rkeep" and A = "rfc_forward_closure ?Rstrict"
        and TA = ?TA and rel = b_rel and c = c and c_opt = c_opt
      ])
    show "left_linear_trs (set (Rdelete @ ?Rkeep)) \<or>
      ta_det ?TA \<and> state_raise_consistent ?TA b_rel"
      using left_linear_b by blast
    show "finite (ta_rules ?TA)" by (rule fin_b)
    show "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))" by (rule compat_delete)
    show "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ?Rkeep))" by (rule compat_keep)
    show "state_coherent ?TA b_rel" by (rule coh_b)
    show "ta_bounded ?TA c" by (rule tab_b)
    show "infinite (UNIV :: 'f set)" by (rule inf)
    show "wf_trs (set Rdelete \<union> set ?Rkeep)" by (rule wf_b)
    show "\<And>l r. (l, r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l" by (rule nondup)
    show "weak_kind_condition c c_opt (set Rdelete)" by (rule wkc_b)
    show "\<And>t. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow>
      \<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
        (\<exists>qf\<in>ta_final ?TA.
          qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
      by (rule rfc_acc)
  qed
qed

lemma rfc_native_matchbox_relative_bounds_SN_on:
  fixes info :: "('f::{linorder,showl,compare_order},
    'q::{compare_order,showl}) bounds_info"
  assumes spec: "tp_spec I"
    and ok: "isOK (rfc_native_matchbox_relative_bounds_tt
      I info initial_terms Rdelete tp)"
    and inf: "infinite (UNIV :: 'f set)"
  shows "SN_on
    (relto (rstep (set Rdelete))
      (rstep (set (ceta_list_diff (tp_ops.R I tp) Rdelete))))
    (rfc_forward_closure (tp_ops.R I tp))"
proof -
  interpret tp_spec I by (rule spec)
  obtain bi ren where ren: "get_integer_bounds_info info = (bi,ren)"
    by (cases "get_integer_bounds_info info") auto
  obtain type c qfin preTA rel where info':
    "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi) auto
  have info_eq: "get_integer_bounds_info info =
      (Bounds_Info type c qfin preTA rel,ren)"
    using ren info' by simp
  let ?Rstrict = "R tp"
  let ?Rkeep = "ceta_list_diff ?Rstrict Rdelete"
  let ?states = "remdups (states_of_tree_automata_dup preTA)"
  from ok[unfolded rfc_native_matchbox_relative_bounds_tt_def
      ren info' Let_def]
  obtain TA where TA: "generate_ta_cond preTA rel = return TA"
    and okb: "isOK (check_bounds_generic_native_rfc_relative
      info Rdelete ?Rkeep)"
    by auto
  from generate_ta_cond[OF TA] have inv0:
    "ta_inv TA (rel_checker rel) (relation_of rel)"
    and TA_gen: "TA = generate_ta preTA"
    by auto
  from check_bounds_generic_native_rfc_relative_exact[
      OF okb info_eq]
  obtain c_opt where type: "type = Match"
    and rel: "rel = Id_Relation"
    and left_linear: "left_linear_trs (set (Rdelete @ ?Rkeep))"
    and finite: "finite (ta_rules
      (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta))"
    and compat_keep: "state_compatible
      (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) Id
      (cover_bound c Matchbounds.match (Weak_TRS c_opt)
        (set ?Rkeep))"
    and bounded: "ta_bounded
      (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta) c"
    and qfin_rhs: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states
      (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
    and qfin_final: "set qfin \<subseteq> ta_final
      (ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
    and wf: "wf_trs (set Rdelete \<union> set ?Rkeep)"
    and nondup0: "\<forall>l r. (l,r) \<in> set (Rdelete @ ?Rkeep) \<longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l"
    and weak: "weak_kind_condition c c_opt (set Rdelete)"
    by blast
  have bt: "boundstype info = Match"
    using boundstype_get_integer_bounds_info[OF info_eq] type by auto
  have inv: "ta_inv TA (rel_checker Id_Relation) Id"
    using inv0 unfolding rel by simp
  let ?TA = "(ta_of (generate_ta preTA) ::
    (integer,'f \<times> nat)ta)"
  from ok[unfolded rfc_native_matchbox_relative_bounds_tt_def
      ren info' Let_def]
  have initial_covers: "rfc_initial_covers ?Rstrict initial_terms"
    and initial_acc0: "rfc_initial_paired_accepted_impl
      TYPE('f) (projr (generate_ta_cond preTA rel))
      qfin initial_terms"
    and closed0: "rfc_native_matchbox_closed_impl
      (projr (generate_ta_cond preTA rel))
      Id_Relation ?states ?Rstrict"
    and ext0: "rfc_native_matchbox_ext_right_impl
      (projr (generate_ta_cond preTA rel))
      Id_Relation ?states ?Rstrict"
    and splice0: "rfc_native_inner_splice_impl
      (projr (generate_ta_cond preTA rel)) ?states c Rdelete"
    and no_top0: "rfc_native_no_top_redex_impl
      (projr (generate_ta_cond preTA rel)) ?states c Rdelete"
    and qfin_rhs0: "list_all
      (\<lambda>q. rs.memb q (ta_rhs_states_set
        (projr (generate_ta_cond preTA rel)))) qfin"
    by auto
  have initial_acc: "rfc_initial_paired_accepted_impl
      TYPE('f) TA qfin initial_terms"
    using initial_acc0 TA by simp
  have closed: "rfc_native_matchbox_closed_impl
      TA Id_Relation ?states ?Rstrict"
    using closed0 TA by simp
  have ext: "rfc_native_matchbox_ext_right_impl
      TA Id_Relation ?states ?Rstrict"
    using ext0 TA by simp
  have splice: "rfc_native_inner_splice_impl
      TA ?states c Rdelete"
    using splice0 TA by simp
  have no_top: "rfc_native_no_top_redex_impl
      TA ?states c Rdelete"
    using no_top0 TA by simp
  have state_cover: "ta_states ?TA \<subseteq> set ?states"
    using ta_states_generate_ta_states_of_tree_automata_dup by auto
  have state_cover_impl: "ta_states (ta_of TA) \<subseteq> set ?states"
    using state_cover unfolding TA_gen .
  have compat_delete: "state_compatible ?TA Id
      (cover_bound c Matchbounds.match Strict_TRS
        (set Rdelete))"
    using rfc_native_inner_splice_full_strict_compat[
      OF inv state_cover_impl splice no_top]
    unfolding TA_gen .
  have qfin_rhs_impl: "set qfin \<subseteq> ta_rhs_states (ta_of TA)"
    using qfin_rhs0 TA ta_inv.ta_rhs_states_set[OF inv]
    by (auto simp: list_all_iff rs.correct)
  have wf_strict: "wf_trs (set ?Rstrict)"
  proof -
    from ok[unfolded rfc_native_matchbox_relative_bounds_tt_def
        ren info' Let_def]
    show ?thesis by auto
  qed
  have rfc_acc: "\<And>t. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow>
    \<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
      (\<exists>qf\<in>ta_final ?TA. qf \<in> ta_res ?TA
        (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
  proof -
    fix t
    assume t: "t \<in> rfc_forward_closure ?Rstrict"
    from rfc_native_matchbox_paired_forward_closure_accepted[
      OF inv state_cover_impl closed ext wf_strict initial_covers
        initial_acc _ t]
    obtain q qf where q: "q \<in> set qfin"
      and qf: "qf \<in> ta_final (ta_of TA)"
      and acc: "qf \<in> ta_res (ta_of TA)
        (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      using qfin_final unfolding TA_gen by blast
    show "\<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
      (\<exists>qf\<in>ta_final ?TA. qf \<in> ta_res ?TA
        (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
      using q qf acc qfin_rhs_impl qfin_final
      unfolding TA_gen by blast
  qed
  have nondup: "\<And>l r.
    (l,r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
    vars_term_ms r \<subseteq># vars_term_ms l"
    using nondup0 by auto
  show ?thesis
  proof (rule rfc_relative_bounds_impl_semantic_exists[
      where R = Rdelete and S = ?Rkeep
        and A = "rfc_forward_closure ?Rstrict"
        and TA = ?TA and rel = Id and c = c and c_opt = c_opt])
    show "left_linear_trs (set (Rdelete @ ?Rkeep)) \<or>
      ta_det ?TA \<and> state_raise_consistent ?TA Id"
      using left_linear by blast
    show "finite (ta_rules ?TA)" by (rule finite)
    show "state_compatible ?TA Id
      (cover_bound c Matchbounds.match Strict_TRS (set Rdelete))"
      by (rule compat_delete)
    show "state_compatible ?TA Id
      (cover_bound c Matchbounds.match (Weak_TRS c_opt)
        (set ?Rkeep))"
      by (rule compat_keep)
    show "state_coherent ?TA Id" by (rule state_coherent_Id)
    show "ta_bounded ?TA c" by (rule bounded)
    show "infinite (UNIV :: 'f set)" by (rule inf)
    show "wf_trs (set Rdelete \<union> set ?Rkeep)" by (rule wf)
    show "\<And>l r. (l,r) \<in> set Rdelete \<union> set ?Rkeep \<Longrightarrow>
      vars_term_ms r \<subseteq># vars_term_ms l"
      by (rule nondup)
    show "weak_kind_condition c c_opt (set Rdelete)" by (rule weak)
    show "\<And>t. t \<in> rfc_forward_closure ?Rstrict \<Longrightarrow>
      \<exists>q. q \<in> ta_rhs_states ?TA \<and> q \<in> ta_final ?TA \<and>
        (\<exists>qf\<in>ta_final ?TA. qf \<in> ta_res ?TA
          (map_vars_term (\<lambda>_. q) (lift_term 0 t)))"
      by (rule rfc_acc)
  qed
qed

lemma rfc_automaton_closed_relative_bounds_tt:
  fixes info :: "('f::{linorder,showl,compare_order}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I"
    and res: "rfc_automaton_closed_relative_bounds_tt I info initial_terms Rdelete tp = return tp'"
    and inf: "infinite (UNIV :: 'f set)"
    and rec: "SN_qrel (tp_ops.qreltrs I tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  obtain bi ren where ren: "get_integer_bounds_info info = (bi, ren)"
    by (cases "get_integer_bounds_info info", auto)
  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, auto)
  let ?Rstrict = "R tp"
  let ?Rdelete = "set Rdelete"
  let ?Rkeep = "set (ceta_list_diff ?Rstrict Rdelete)"
  from res[unfolded rfc_automaton_closed_relative_bounds_tt_def ren info' Let_def]
  have ok: "isOK (rfc_automaton_closed_relative_bounds_tt I info initial_terms Rdelete tp)"
    unfolding rfc_automaton_closed_relative_bounds_tt_def ren info' Let_def isOK_def by simp
  from res[unfolded rfc_automaton_closed_relative_bounds_tt_def ren info' Let_def]
  have qempty: "Q_empty tp"
    and qlist: "Q tp = []"
    and rwempty: "Rw tp = []"
    and nfs: "\<not> NFS tp"
    and sub: "?Rdelete \<subseteq> set ?Rstrict"
    and wfR: "wf_trs (set ?Rstrict)"
    and rlin_list: "list_all (\<lambda>(l,r). linear_term r) ?Rstrict"
    and tp': "tp' = mk (NFS tp) (Q tp) (ceta_list_diff ?Rstrict Rdelete) Rdelete"
    by (auto simp: Q_empty_sound isOK_check_allm split: if_splits sum_bind_splits)
  have rlinR: "\<And>lr. lr \<in> set ?Rstrict \<Longrightarrow> linear_term (snd lr)"
    using rlin_list by (auto simp: list_all_iff split: prod.splits)
  have union_id: "?Rdelete \<union> ?Rkeep = set ?Rstrict"
    using sub by auto
  have Q_empty_set: "set (Q tp) = {}"
    using qlist by simp
  have NFS_false: "NFS tp = False"
    using nfs by simp
  from rfc_automaton_closed_relative_bounds_SN_on[OF \<open>tp_spec I\<close> ok inf]
  have sn_rfc: "SN_on (relto (rstep ?Rdelete) (rstep ?Rkeep))
      (right_forw_closure string_rename (?Rdelete \<union> ?Rkeep))"
    unfolding rfc_forward_closure_eq union_id .
  have rec_rel: "SN_rel (rstep ?Rkeep) (rstep ?Rdelete)"
    using rec unfolding tp' qreltrs_sound SN_qrel_def split NFS_false qlist by simp
  have wfDK: "wf_trs (?Rdelete \<union> ?Rkeep)"
    using wfR unfolding union_id .
  have rlinDK: "\<And>lr. lr \<in> ?Rdelete \<union> ?Rkeep \<Longrightarrow> linear_term (snd lr)"
    using rlinR unfolding union_id by auto
  have sn_del: "SN_rel (rstep ?Rdelete) (rstep ?Rkeep)"
    by (rule SN_rel_from_RFC_delete_and_reverse_residual[OF wfDK rlinDK sn_rfc rec_rel])
  have sn_keep_empty: "SN_rel (rstep (set ?Rstrict - ?Rdelete)) (rstep ({} :: ('f,string)trs))"
  proof -
    have "set ?Rstrict - ?Rdelete = ?Rkeep"
      by auto
    moreover have "SN_rel (rstep ?Rkeep) (rstep ({} :: ('f,string)trs))"
      by (rule SN_rel_mono[OF subset_refl _ rec_rel], auto)
    ultimately show ?thesis by simp
  qed
  have del_inter: "?Rdelete \<inter> set ?Rstrict = ?Rdelete"
    using sub by auto
  have del_inter_union: "?Rdelete \<inter> (set ?Rstrict \<union> {}) = ?Rdelete"
    using sub by auto
  have keep_diff: "set ?Rstrict - ?Rdelete = ?Rkeep"
    by auto
  have keep_diff_union: "set ?Rstrict \<union> {} - ?Rdelete = ?Rkeep"
    by auto
  have sn_split: "SN_qrel (False, {}, set ?Rstrict, ({} :: ('f,string)trs))"
  proof (rule SN_qrel_split[where D = ?Rdelete])
    show "SN_qrel (False, {}, ?Rdelete \<inter> (set ?Rstrict \<union> {}), set ?Rstrict \<union> {} - ?Rdelete)"
      unfolding SN_qrel_def del_inter_union keep_diff_union
      using sn_del by simp
    show "SN_qrel (False, {}, set ?Rstrict - ?Rdelete, {} - ?Rdelete)"
      using sn_keep_empty by (simp add: SN_qrel_def)
  qed
  show ?thesis
    using sn_split unfolding qreltrs_sound SN_qrel_def split NFS_false qlist rwempty by simp
qed

lemma rfc_matchbox_relative_bounds_tt:
  fixes info :: "('f::{linorder,showl,compare_order}, 'q::{compare_order,showl}) bounds_info"
  assumes "tp_spec I"
    and res: "rfc_matchbox_relative_bounds_tt I info initial_terms Rdelete tp = return tp'"
    and inf: "infinite (UNIV :: 'f set)"
    and rec: "SN_qrel (tp_ops.qreltrs I tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  let ?pinfo = "info"
  obtain bi ren where ren: "get_integer_bounds_info ?pinfo = (bi, ren)"
    by (cases "get_integer_bounds_info ?pinfo", auto)
  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, auto)
  let ?Rstrict = "R tp"
  let ?Rdelete = "set Rdelete"
  let ?Rkeep = "set (ceta_list_diff ?Rstrict Rdelete)"
  from res[unfolded rfc_matchbox_relative_bounds_tt_def ren info' Let_def]
  have ok: "isOK (rfc_matchbox_relative_bounds_tt I info initial_terms Rdelete tp)"
    unfolding rfc_matchbox_relative_bounds_tt_def ren info' Let_def isOK_def by simp
  from res[unfolded rfc_matchbox_relative_bounds_tt_def ren info' Let_def]
  have qempty: "Q_empty tp"
    and qlist: "Q tp = []"
    and rwempty: "Rw tp = []"
    and nfs: "\<not> NFS tp"
    and sub: "?Rdelete \<subseteq> set ?Rstrict"
    and wfR: "wf_trs (set ?Rstrict)"
    and rlin_list: "list_all (\<lambda>(l,r). linear_term r) ?Rstrict"
    and tp': "tp' = mk (NFS tp) (Q tp) (ceta_list_diff ?Rstrict Rdelete) Rdelete"
    by (auto simp: Q_empty_sound isOK_check_allm split: if_splits sum_bind_splits)
  have rlinR: "\<And>lr. lr \<in> set ?Rstrict \<Longrightarrow> linear_term (snd lr)"
    using rlin_list by (auto simp: list_all_iff split: prod.splits)
  have union_id: "?Rdelete \<union> ?Rkeep = set ?Rstrict"
    using sub by auto
  have NFS_false: "NFS tp = False"
    using nfs by simp
  from rfc_matchbox_relative_bounds_SN_on[OF \<open>tp_spec I\<close> ok inf]
  have sn_rfc: "SN_on (relto (rstep ?Rdelete) (rstep ?Rkeep))
      (right_forw_closure string_rename (?Rdelete \<union> ?Rkeep))"
    unfolding rfc_forward_closure_eq union_id .
  have rec_rel: "SN_rel (rstep ?Rkeep) (rstep ?Rdelete)"
    using rec unfolding tp' qreltrs_sound SN_qrel_def split NFS_false qlist by simp
  have wfDK: "wf_trs (?Rdelete \<union> ?Rkeep)"
    using wfR unfolding union_id .
  have rlinDK: "\<And>lr. lr \<in> ?Rdelete \<union> ?Rkeep \<Longrightarrow> linear_term (snd lr)"
    using rlinR unfolding union_id by auto
  have sn_del: "SN_rel (rstep ?Rdelete) (rstep ?Rkeep)"
    by (rule SN_rel_from_RFC_delete_and_reverse_residual[OF wfDK rlinDK sn_rfc rec_rel])
  have sn_keep_empty: "SN_rel (rstep (set ?Rstrict - ?Rdelete)) (rstep ({} :: ('f,string)trs))"
  proof -
    have "set ?Rstrict - ?Rdelete = ?Rkeep"
      by auto
    moreover have "SN_rel (rstep ?Rkeep) (rstep ({} :: ('f,string)trs))"
      by (rule SN_rel_mono[OF subset_refl _ rec_rel], auto)
    ultimately show ?thesis by simp
  qed
  have del_inter_union: "?Rdelete \<inter> (set ?Rstrict \<union> {}) = ?Rdelete"
    using sub by auto
  have keep_diff_union: "set ?Rstrict \<union> {} - ?Rdelete = ?Rkeep"
    by auto
  have sn_split: "SN_qrel (False, {}, set ?Rstrict, ({} :: ('f,string)trs))"
  proof (rule SN_qrel_split[where D = ?Rdelete])
    show "SN_qrel (False, {}, ?Rdelete \<inter> (set ?Rstrict \<union> {}), set ?Rstrict \<union> {} - ?Rdelete)"
      unfolding SN_qrel_def del_inter_union keep_diff_union
      using sn_del by simp
    show "SN_qrel (False, {}, set ?Rstrict - ?Rdelete, {} - ?Rdelete)"
      using sn_keep_empty by (simp add: SN_qrel_def)
  qed
  show ?thesis
    using sn_split unfolding qreltrs_sound SN_qrel_def split NFS_false qlist rwempty by simp
qed

lemma rfc_native_matchbox_relative_bounds_tt:
  fixes info :: "('f::{linorder,showl,compare_order},
    'q::{compare_order,showl}) bounds_info"
  assumes spec: "tp_spec I"
    and res: "rfc_native_matchbox_relative_bounds_tt
      I info initial_terms Rdelete tp = return tp'"
    and inf: "infinite (UNIV :: 'f set)"
    and rec: "SN_qrel (tp_ops.qreltrs I tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by (rule spec)
  obtain bi ren where ren: "get_integer_bounds_info info = (bi,ren)"
    by (cases "get_integer_bounds_info info") auto
  obtain type c qfin preTA rel where info':
    "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi) auto
  let ?Rstrict = "R tp"
  let ?Rdelete = "set Rdelete"
  let ?Rkeep = "set (ceta_list_diff ?Rstrict Rdelete)"
  from res[unfolded rfc_native_matchbox_relative_bounds_tt_def
      ren info' Let_def]
  have ok: "isOK (rfc_native_matchbox_relative_bounds_tt
      I info initial_terms Rdelete tp)"
    unfolding rfc_native_matchbox_relative_bounds_tt_def
      ren info' Let_def isOK_def
    by simp
  from res[unfolded rfc_native_matchbox_relative_bounds_tt_def
      ren info' Let_def]
  have qlist: "Q tp = []"
    and rwempty: "Rw tp = []"
    and nfs: "\<not> NFS tp"
    and sub: "?Rdelete \<subseteq> set ?Rstrict"
    and wfR: "wf_trs (set ?Rstrict)"
    and rlin_list: "list_all (\<lambda>(l,r). linear_term r) ?Rstrict"
    and tp': "tp' = mk (NFS tp) (Q tp)
      (ceta_list_diff ?Rstrict Rdelete) Rdelete"
    by (auto simp: Q_empty_sound isOK_check_allm
      split: if_splits sum_bind_splits)
  have rlinR: "\<And>lr. lr \<in> set ?Rstrict \<Longrightarrow>
      linear_term (snd lr)"
    using rlin_list
    by (auto simp: list_all_iff split: prod.splits)
  have union_id: "?Rdelete \<union> ?Rkeep = set ?Rstrict"
    using sub by auto
  have NFS_false: "NFS tp = False"
    using nfs by simp
  from rfc_native_matchbox_relative_bounds_SN_on[
    OF spec ok inf]
  have sn_rfc: "SN_on
      (relto (rstep ?Rdelete) (rstep ?Rkeep))
      (right_forw_closure string_rename
        (?Rdelete \<union> ?Rkeep))"
    unfolding rfc_forward_closure_eq union_id .
  have rec_rel: "SN_rel (rstep ?Rkeep) (rstep ?Rdelete)"
    using rec unfolding tp' qreltrs_sound SN_qrel_def
      split NFS_false qlist by simp
  have wfDK: "wf_trs (?Rdelete \<union> ?Rkeep)"
    using wfR unfolding union_id .
  have rlinDK: "\<And>lr. lr \<in> ?Rdelete \<union> ?Rkeep \<Longrightarrow>
      linear_term (snd lr)"
    using rlinR unfolding union_id by auto
  have sn_del: "SN_rel (rstep ?Rdelete) (rstep ?Rkeep)"
    by (rule SN_rel_from_RFC_delete_and_reverse_residual[
      OF wfDK rlinDK sn_rfc rec_rel])
  have sn_keep_empty:
    "SN_rel (rstep (set ?Rstrict - ?Rdelete))
      (rstep ({} :: ('f,string)trs))"
  proof -
    have "set ?Rstrict - ?Rdelete = ?Rkeep" by auto
    moreover have "SN_rel (rstep ?Rkeep)
        (rstep ({} :: ('f,string)trs))"
      by (rule SN_rel_mono[OF subset_refl _ rec_rel]) auto
    ultimately show ?thesis by simp
  qed
  have del: "?Rdelete \<inter> (set ?Rstrict \<union> {}) = ?Rdelete"
    using sub by auto
  have keep: "set ?Rstrict \<union> {} - ?Rdelete = ?Rkeep"
    by auto
  have sn_split:
    "SN_qrel (False,{},set ?Rstrict,({} :: ('f,string)trs))"
  proof (rule SN_qrel_split[where D = ?Rdelete])
    show "SN_qrel (False,{},?Rdelete \<inter> (set ?Rstrict \<union> {}),
      set ?Rstrict \<union> {} - ?Rdelete)"
      unfolding SN_qrel_def del keep using sn_del by simp
    show "SN_qrel (False,{},set ?Rstrict - ?Rdelete,
      {} - ?Rdelete)"
      using sn_keep_empty by (simp add: SN_qrel_def)
  qed
  show ?thesis
    using sn_split unfolding qreltrs_sound SN_qrel_def
      split NFS_false qlist rwempty by simp
qed

definition rfc_relative_bounds_tt ::
  "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{compare_order,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    ('f,string)rules \<Rightarrow>
    'tp \<Rightarrow> 'tp result"
where
  "rfc_relative_bounds_tt I info initial_terms Rdelete tp \<equiv>
    (case get_integer_bounds_info info of
      (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
        TA \<leftarrow> generate_ta_cond preTA rel;
        check (tp_ops.Q_empty I tp)
          (showsl_lit (STR ''RFC relative bounds currently require an empty Q component''));
        check (tp_ops.Rw I tp = [])
          (showsl_lit (STR ''RFC relative bounds currently require no weak rules''));
        check (\<not> tp_ops.nfs I tp)
          (showsl_lit (STR ''RFC relative bounds currently certify full rewriting, not innermost rewriting''));
        check (Rdelete = tp_ops.R I tp)
          (showsl_lit (STR ''RFC relative bounds currently require deleting exactly all strict rules''));
        check_wf_trs (tp_ops.R I tp);
        check (list_all (\<lambda>(l,r). linear_term r) (tp_ops.R I tp))
          (showsl_lit (STR ''RFC relative bounds require right-linear removed rules''));
        check (Matchbounds_Impl.rfc_initial_single_var initial_terms)
          (showsl_lit (STR ''RFC relative bounds finite initial language templates must contain at most one variable''));
        check (Matchbounds_Impl.rfc_initial_covers (tp_ops.R I tp) initial_terms)
          (showsl_lit (STR ''RFC relative initial language does not contain all removed-rule right-hand sides''));
        check (Matchbounds_Impl.rfc_initial_closed (tp_ops.R I tp) initial_terms)
          (showsl_lit (STR ''RFC relative initial language is not closed under removed-rule one-step right-forward narrowing''));
        check (Matchbounds_Impl.rfc_initial_accepted_with_tail_states_impl
          TYPE('f) TA qfin initial_terms)
          (showsl_lit (STR ''RFC relative finite initial language is not accepted by the automaton for all tail states''));
        check_bounds_generic_without_contains info (tp_ops.R I tp) [];
        return (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) [] Rdelete)
      })"

lemma rfc_relative_bounds_tt:
  fixes info :: "('f::{compare_order,showl}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I"
    and res: "rfc_relative_bounds_tt I info initial_terms Rdelete tp = return tp'"
    and inf: "infinite (UNIV :: 'f set)"
    and rec: "SN_qrel (tp_ops.qreltrs I tp')"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  obtain bi ren where ren: "get_integer_bounds_info info = (bi,ren)"
    by (cases "get_integer_bounds_info info") auto
  obtain type c qfin preTA rel where info':
    "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi) auto
  from res[unfolded rfc_relative_bounds_tt_def ren info' Let_def]
  have ok: "isOK (Matchbounds_Impl.rfc_bounds_tt
      I info initial_terms tp)"
    unfolding Matchbounds_Impl.rfc_bounds_tt_def ren info' Let_def
    by (auto simp: Q_empty_sound split: if_splits)
  from Matchbounds_Impl.rfc_bounds_tt[OF \<open>tp_spec I\<close> ok inf]
  show ?thesis .
qed

definition rfc_automaton_closed_bounds_tt ::
  "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info \<Rightarrow>
    ('f,string)term list \<Rightarrow>
    'tp \<Rightarrow> showsl check"
where
  "rfc_automaton_closed_bounds_tt I info initial_terms tp \<equiv>
    (case get_integer_bounds_info info of (Bounds_Info type c qfin preTA rel, ren) \<Rightarrow> do {
      TA \<leftarrow> generate_ta_cond preTA rel;
      check (tp_ops.Q_empty I tp)
        (showsl_lit (STR ''RFC automaton-closed bounds currently require an empty Q component''));
      check (tp_ops.Rw I tp = [])
        (showsl_lit (STR ''RFC automaton-closed bounds currently require no weak rules''));
      check (\<not> tp_ops.nfs I tp)
        (showsl_lit (STR ''RFC automaton-closed bounds currently certify full rewriting, not innermost rewriting''));
      check_wf_trs (tp_ops.R I tp);
      check (list_all (\<lambda>(l,r). linear_term r) (tp_ops.R I tp))
        (showsl_lit (STR ''RFC automaton-closed bounds require right-linear rules''));
      check (rfc_initial_single_var initial_terms)
        (showsl_lit (STR ''RFC automaton-closed initial language templates must contain at most one variable''));
      check (rfc_initial_covers (tp_ops.R I tp) initial_terms)
        (showsl_lit (STR ''RFC automaton-closed initial language does not contain all right-hand sides''));
      check (rfc_initial_accepted_with_tail_states_impl TYPE('f) TA
        (remdups (states_of_tree_automata_dup preTA)) initial_terms)
        (showsl_lit (STR ''RFC automaton-closed initial language is not accepted by the automaton for all automaton states''));
      check (rfc_automaton_closed_impl TA
        (remdups (states_of_tree_automata_dup preTA)) (tp_ops.R I tp))
        (showsl_lit (STR ''RFC automaton-closed split condition failed''));
      check (rfc_lhs_suffix_total_impl TA
        (remdups (states_of_tree_automata_dup preTA)) (tp_ops.R I tp))
        (showsl_lit (STR ''RFC automaton-closed lhs suffix totality condition failed''));
      check_bounds_generic_without_contains info (tp_ops.R I tp) []
    })"

lemma rfc_automaton_closed_bounds_tt:
  fixes info :: "('f::{linorder,showl}, 'q::{linorder,showl}) bounds_info"
  assumes "tp_spec I"
    and ok: "isOK (rfc_automaton_closed_bounds_tt I info initial_terms tp)"
    and inf: "infinite (UNIV :: 'f set)"
  shows "SN_qrel (tp_ops.qreltrs I tp)"
proof -
  interpret tp_spec I by fact
  obtain bi ren where ren: "get_integer_bounds_info info = (bi, ren)"
    by (cases "get_integer_bounds_info info", auto)
  obtain type c qfin preTA rel where info': "bi = Bounds_Info type c qfin preTA rel"
    by (cases bi, auto)
  have info_eq: "get_integer_bounds_info info = (Bounds_Info type c qfin preTA rel, ren)"
    using ren info' by simp
  from ok[unfolded rfc_automaton_closed_bounds_tt_def ren info' Let_def]
  obtain TA where TA: "generate_ta_cond preTA rel = return TA"
    and okb: "isOK (check_bounds_generic_without_contains info (R tp) [])"
    by auto
  from generate_ta_cond[OF TA] have inv: "ta_inv TA (rel_checker rel) (relation_of rel)"
    and TA_gen: "TA = generate_ta preTA" by auto
  let ?TA = "(ta_of (generate_ta preTA) :: (integer,'f \<times> nat)ta)"
  let ?states = "remdups (states_of_tree_automata_dup preTA)"
  from ok[unfolded rfc_automaton_closed_bounds_tt_def ren info' Let_def]
  have Q: "set (Q tp) = {}"
    and Rw: "set (Rw tp) = {}"
    and nfs: "\<not> NFS tp"
    and rhs_lin_list: "list_all (\<lambda>(l, r). linear_term r) (R tp)"
    and initial_single: "rfc_initial_single_var initial_terms"
    and initial_covers: "rfc_initial_covers (R tp) initial_terms"
    and initial_acc_proj: "rfc_initial_accepted_with_tail_states_impl TYPE('f)
      (projr (generate_ta_cond preTA rel)) ?states initial_terms"
    and closed_proj: "rfc_automaton_closed_impl (projr (generate_ta_cond preTA rel)) ?states (R tp)"
    and suffix_total_proj: "rfc_lhs_suffix_total_impl (projr (generate_ta_cond preTA rel)) ?states (R tp)"
    by (auto simp: Q_empty_sound)
  have rhs_lin: "\<And>lr. lr \<in> set (R tp) \<Longrightarrow> linear_term (snd lr)"
    using rhs_lin_list by (auto simp: list_all_iff split: prod.splits)
  have initial_acc_impl: "rfc_initial_accepted_with_tail_states_impl TYPE('f) TA ?states initial_terms"
    using initial_acc_proj TA by simp
  have closed: "rfc_automaton_closed_impl TA ?states (R tp)"
    using closed_proj TA by simp
  have suffix_total: "rfc_lhs_suffix_total_impl TA ?states (R tp)"
    using suffix_total_proj TA by simp
	  from check_bounds_generic_without_contains_exact[
	    where R = "(R tp :: ('f,string)rules)"
	      and S = "([] :: ('f,string)rules)"
	      and info = info
	      and type = type
	      and c = c
	      and qfin = qfin
	      and preTA = preTA
	      and rel_info = rel
	      and ren = ren,
	    OF okb info_eq]
	  obtain b_rel c_opt where bounds:
	    "(left_linear_trs (set (R tp @ [])) \<or>
	      ta_det ?TA \<and> state_raise_consistent ?TA b_rel)
	    \<and> finite (ta_rules ?TA)
	    \<and> state_compatible ?TA b_rel
	      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))
	    \<and> state_compatible ?TA b_rel
	      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set ([] :: ('f,string)rules)))
	    \<and> state_coherent ?TA b_rel
	    \<and> ta_bounded ?TA c
	    \<and> (\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA)
	    \<and> set qfin \<subseteq> ta_final ?TA
	    \<and> wf_trs (set (R tp) \<union> set [])
	    \<and> isOK (bounds_condition (boundstype info) (R tp @ []))"
	    by auto
	  have choice_b: "left_linear_trs (set (R tp @ [])) \<or>
	      ta_det ?TA \<and> state_raise_consistent ?TA b_rel"
	    using bounds by blast
	  have fin_b: "finite (ta_rules ?TA)"
	    using bounds by blast
	  have compat_b: "state_compatible ?TA b_rel
	      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))"
	    using bounds by blast
	  have coh_b: "state_coherent ?TA b_rel"
	    using bounds by blast
	  have tab_b: "ta_bounded ?TA c"
	    using bounds by blast
	  have qfin_b: "\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA"
	    using bounds by blast
	  have qfin_final_b: "set qfin \<subseteq> ta_final ?TA"
	    using bounds by blast
	  have wf_b: "wf_trs (set (R tp) \<union> set [])"
	    using bounds by blast
	  have cond_raw: "isOK (bounds_condition (boundstype info) (R tp @ []))"
	    using bounds by blast
  have cond: "isOK (bounds_condition (boundstype info) (R tp))"
    using cond_raw by simp
	  have state_cover: "ta_states ?TA \<subseteq> set ?states"
	    using ta_states_generate_ta_states_of_tree_automata_dup by auto
	  have state_cover_impl: "ta_states (ta_of TA) \<subseteq> set ?states"
	    using state_cover unfolding TA_gen .
  have initial_acc_all: "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> ta_states ?TA \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  proof -
    fix t q
    assume t: "t \<in> set initial_terms" and q: "q \<in> ta_states ?TA"
    have q_list: "q \<in> set ?states"
      using state_cover q by auto
    from rfc_initial_accepted_with_tail_states_impl[OF inv initial_acc_impl t q_list]
    show "\<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      unfolding TA_gen .
	  qed
	  have initial_acc_all_impl:
	    "\<And>t q. t \<in> set initial_terms \<Longrightarrow> q \<in> ta_states (ta_of TA) \<Longrightarrow>
	      \<exists>qf\<in>ta_final (ta_of TA).
	        qf \<in> ta_res (ta_of TA) (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
	    using initial_acc_all unfolding TA_gen .
	  have rfc_acc: "\<And>t q. t \<in> rfc_forward_closure (R tp) \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
  proof -
    fix t q
    assume t: "t \<in> rfc_forward_closure (R tp)" and q: "q \<in> set qfin"
	    have q_state: "q \<in> ta_states ?TA"
	      using q qfin_final_b unfolding ta_states_def by auto
	    have q_state_impl: "q \<in> ta_states (ta_of TA)"
	      using q_state unfolding TA_gen .
	    from rfc_automaton_closed_forward_closure_accepted[
	      OF inv state_cover_impl closed suffix_total initial_covers initial_acc_all_impl t q_state_impl]
    show "\<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      unfolding TA_gen .
  qed
  have wf_R: "wf_trs (set (R tp))"
    using wf_b by simp
  have local_SN: "locally_terminating
      (cover (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)) \<union> Matchbounds.raise)"
    using bounds_condition[OF cond] wf_R by auto
  have SN_r: "SN (rstep (set (R tp)))"
  proof (rule rfc_bounds_impl_semantic[
      where R = "R tp" and S = "[]" and TA = ?TA and rel = b_rel
        and e = "boundstype_fun (boundstype info)" and c = c and c_opt = c_opt
        and qfin = "set qfin"])
    show "left_linear_trs (set (R tp @ [])) \<or>
      ta_det ?TA \<and> state_raise_consistent ?TA b_rel" by (rule choice_b)
    show "finite (ta_rules ?TA)" by (rule fin_b)
    show "state_compatible ?TA b_rel
      (cover_bound c (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)))" by (rule compat_b)
    show "state_compatible ?TA b_rel
      (cover_bound c Matchbounds.match (Weak_TRS c_opt) (set []))"
      unfolding state_compatible_def cover_bound_def by auto
    show "state_coherent ?TA b_rel" by (rule coh_b)
    show "ta_bounded ?TA c" by (rule tab_b)
    show "\<exists>q\<in>set qfin. q \<in> ta_rhs_states ?TA" by (rule qfin_b)
    show "set qfin \<subseteq> ta_final ?TA" by (rule qfin_final_b)
    show "infinite (UNIV :: 'f set)" by (rule inf)
    show "wf_trs (set (R tp) \<union> set [])" by (rule wf_b)
    show "locally_terminating
      (cover (boundstype_fun (boundstype info)) Strict_TRS (set (R tp)) \<union> Matchbounds.raise)"
      by (rule local_SN)
    show "\<And>lr. lr \<in> set (R tp) \<Longrightarrow> linear_term (snd lr)" by (rule rhs_lin)
    show "\<And>t q. t \<in> rfc_forward_closure (R tp) \<Longrightarrow> q \<in> set qfin \<Longrightarrow>
      \<exists>qf\<in>ta_final ?TA.
        qf \<in> ta_res ?TA (map_vars_term (\<lambda>_. q) (lift_term 0 t))"
      by (rule rfc_acc)
  qed
  then have SN: "SN_qrel (NFS tp, {}, set (R tp), {})"
    using nfs by simp
  show ?thesis unfolding qreltrs_sound Q Rw
    by (rule SN)
qed

end
