theory QDP_To_SRS_Zantema
  imports
    TRS.QDP_Framework
    Knuth_Bendix_Order.Lexicographic_Extension
begin

text \<open>
  A certifiable form of the two-stack QDP-to-SRS transformation used by
  AProVE. The definitions describe symbol roles rather than benchmark names:
  one binary state symbol, unary stack symbols, productive pairs, and
  left-to-right transfer pairs.
\<close>

fun unary_prefix :: "('f, 'v) term \<Rightarrow> 'f list" where
  "unary_prefix (Var x) = []"
| "unary_prefix (Fun f [t]) = f # unary_prefix t"
| "unary_prefix (Fun f ts) = []"

fun unary_term :: "'f list \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "unary_term [] t = t"
| "unary_term (f # fs) t = Fun f [unary_term fs t]"

lemma unary_term_append[simp]:
  "unary_term (xs @ ys) t = unary_term xs (unary_term ys t)"
  by (induct xs) auto

lemma unary_prefix_unary_term[simp]:
  "unary_prefix (unary_term xs t) = xs @ unary_prefix t"
  by (induct xs) auto

lemma subst_unary_term[simp]:
  "unary_term xs t \<cdot> \<sigma> = unary_term xs (t \<cdot> \<sigma>)"
  by (induct xs) auto

definition zantema_encode ::
  "'v \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "zantema_encode z t = (case t of
      Fun f [l, r] \<Rightarrow>
        unary_term (rev (unary_prefix l) @ unary_prefix r) (Var z)
    | _ \<Rightarrow> Var z)"

definition zantema_left_depth :: "('f, 'v) term \<Rightarrow> nat" where
  "zantema_left_depth t = (case t of
      Fun f [l, r] \<Rightarrow> length (unary_prefix l)
    | _ \<Rightarrow> 0)"

definition zantema_productive_pair ::
  "('f, 'v) rule \<Rightarrow> bool" where
  "zantema_productive_pair lr \<longleftrightarrow>
    (\<exists>f x y lhs rhs.
       x \<noteq> y \<and> lhs \<noteq> [] \<and> rhs \<noteq> [] \<and>
       lr = (Fun f [Var x, unary_term lhs (Var y)],
             Fun f [unary_term rhs (Var x), Var y]))"

definition zantema_transfer_pair ::
  "('f, 'v) rule \<Rightarrow> bool" where
  "zantema_transfer_pair lr \<longleftrightarrow>
    (\<exists>f a x y.
       x \<noteq> y \<and>
       lr = (Fun f [Fun a [Var x], Var y],
             Fun f [Var x, Fun a [Var y]]))"

definition zantema_srs :: "('f, 'v) trs \<Rightarrow> ('f, 'v) trs" where
  "zantema_srs P =
    {(unary_term lhs (Var x), unary_term (rev rhs) (Var x)) |
       lr f x y lhs rhs.
       lr \<in> P \<and> x \<noteq> y \<and> lhs \<noteq> [] \<and> rhs \<noteq> [] \<and>
       lr = (Fun f [Var x, unary_term lhs (Var y)],
             Fun f [unary_term rhs (Var x), Var y])}"

fun dest_unary_var :: "('f, 'v) term \<Rightarrow> ('f list \<times> 'v) option" where
  "dest_unary_var (Var x) = Some ([],x)"
| "dest_unary_var (Fun f [t]) =
    map_option (\<lambda>(fs,x). (f # fs,x)) (dest_unary_var t)"
| "dest_unary_var (Fun f ts) = None"

fun zantema_pair_impl ::
  "('f::equal, 'v::equal) rule \<Rightarrow>
    (('f, 'v) rule option) option" where
  "zantema_pair_impl
      (Fun f [Var x,t], Fun g [s,Var y]) =
    (if f = g \<and> x \<noteq> y then
       (case (dest_unary_var t, dest_unary_var s) of
          (Some (lhs,y'), Some (rhs,x')) \<Rightarrow>
            if y' = y \<and> x' = x \<and> lhs \<noteq> [] \<and> rhs \<noteq> []
            then Some (Some
              (unary_term lhs (Var x), unary_term (rev rhs) (Var x)))
            else None
        | _ \<Rightarrow> None)
     else None)"
| "zantema_pair_impl
      (Fun f [Fun a [Var x],Var y], Fun g [Var x',Fun b [Var y']]) =
    (if f = g \<and> a = b \<and> x = x' \<and> y = y' \<and> x \<noteq> y
     then Some None else None)"
| "zantema_pair_impl lr = None"

fun zantema_transform_impl ::
  "(('f::equal, 'v::equal) rule) list \<Rightarrow> (('f, 'v) rule list) option" where
  "zantema_transform_impl [] = Some []"
| "zantema_transform_impl (lr # P) =
    (case (zantema_pair_impl lr, zantema_transform_impl P) of
       (Some None, Some S) \<Rightarrow> Some S
     | (Some (Some r), Some S) \<Rightarrow> Some (r # S)
     | _ \<Rightarrow> None)"

lemma unary_term_eq_Var_iff[simp]:
  "unary_term fs (Var x) = Var y \<longleftrightarrow> fs = [] \<and> x = y"
  by (cases fs) auto

lemma Var_eq_unary_term_iff[simp]:
  "Var y = unary_term fs (Var x) \<longleftrightarrow> fs = [] \<and> x = y"
  by (cases fs) auto

lemma unary_term_eq_Fun_iff[simp]:
  "unary_term fs (Var x) = Fun f ts \<longleftrightarrow>
    (\<exists>gs. fs = f # gs \<and> ts = [unary_term gs (Var x)])"
  by (cases fs) auto

lemma Fun_eq_unary_term_iff[simp]:
  "Fun f ts = unary_term fs (Var x) \<longleftrightarrow>
    (\<exists>gs. fs = f # gs \<and> ts = [unary_term gs (Var x)])"
  by (cases fs) auto

lemma unary_term_inject[simp]:
  "unary_term fs (Var x) = unary_term gs (Var y) \<longleftrightarrow>
    fs = gs \<and> x = y"
  by (induct fs arbitrary: gs) (case_tac gs; auto)+

lemma dest_unary_var_Some_iff:
  "dest_unary_var t = Some (fs,x) \<longleftrightarrow> t = unary_term fs (Var x)"
  by (induct t arbitrary: fs x rule: dest_unary_var.induct)
     (auto split: option.splits prod.splits)

lemma zantema_pair_impl_productive:
  assumes "zantema_pair_impl lr = Some (Some r)"
  shows "zantema_productive_pair lr"
    and "r \<in> zantema_srs {lr}"
  using assms
  unfolding zantema_productive_pair_def zantema_srs_def
  by (induct lr rule: zantema_pair_impl.induct)
     (auto simp: dest_unary_var_Some_iff
       split: option.splits prod.splits if_splits)+

lemma zantema_pair_impl_transfer:
  assumes "zantema_pair_impl lr = Some None"
  shows "zantema_transfer_pair lr"
  using assms unfolding zantema_transfer_pair_def
  by (induct lr rule: zantema_pair_impl.induct)
     (auto simp: dest_unary_var_Some_iff
       split: option.splits prod.splits if_splits)

lemma zantema_pair_impl_productive_srs:
  assumes "zantema_pair_impl lr = Some (Some r)"
  shows "zantema_srs {lr} = {r}"
  using assms unfolding zantema_srs_def
  by (induct lr rule: zantema_pair_impl.induct)
     (auto simp: dest_unary_var_Some_iff
       split: option.splits prod.splits if_splits)

lemma zantema_pair_impl_transfer_srs:
  assumes "zantema_pair_impl lr = Some None"
  shows "zantema_srs {lr} = {}"
  using assms unfolding zantema_srs_def
  by (induct lr rule: zantema_pair_impl.induct)
     (auto simp: dest_unary_var_Some_iff
       split: option.splits prod.splits if_splits)

lemma zantema_srs_insert:
  "zantema_srs (insert lr P) = zantema_srs {lr} \<union> zantema_srs P"
  unfolding zantema_srs_def by blast

lemma zantema_transform_impl_sound:
  assumes "zantema_transform_impl P = Some S"
  shows "set S = zantema_srs (set P) \<and>
    (\<forall>lr \<in> set P.
      zantema_productive_pair lr \<or> zantema_transfer_pair lr)"
  using assms
proof (induct P arbitrary: S)
  case Nil
  then show ?case unfolding zantema_srs_def by auto
next
  case (Cons lr P)
  have head_some: "\<exists>result. zantema_pair_impl lr = Some result"
    using Cons.prems by (cases "zantema_pair_impl lr") auto
  then obtain result where head: "zantema_pair_impl lr = Some result" by blast
  have rec_some: "\<exists>S'. zantema_transform_impl P = Some S'"
    using Cons.prems head by (cases result; cases "zantema_transform_impl P") auto
  then obtain S' where rec: "zantema_transform_impl P = Some S'" by blast
  from Cons.hyps[OF rec] have IH:
    "set S' = zantema_srs (set P)"
    "\<forall>p \<in> set P. zantema_productive_pair p \<or> zantema_transfer_pair p"
    by auto
  show ?case
  proof (cases result)
    case None
    with head rec Cons.prems have S: "S = S'" by simp
    have transfer: "zantema_transfer_pair lr"
      by (rule zantema_pair_impl_transfer[OF head[unfolded None]])
    have empty: "zantema_srs {lr} = {}"
      by (rule zantema_pair_impl_transfer_srs[OF head[unfolded None]])
    have eq: "set S = zantema_srs (set (lr # P))"
      using IH(1) empty zantema_srs_insert[of lr "set P"] by (simp add: S)
    have shapes: "\<forall>p \<in> set (lr # P).
        zantema_productive_pair p \<or> zantema_transfer_pair p"
      using transfer IH(2) by simp
    show ?thesis using eq shapes by blast
  next
    case (Some r)
    with head rec Cons.prems have S: "S = r # S'" by simp
    have productive: "zantema_productive_pair lr"
      by (rule zantema_pair_impl_productive(1)[OF head[unfolded Some]])
    have singleton: "zantema_srs {lr} = {r}"
      by (rule zantema_pair_impl_productive_srs[OF head[unfolded Some]])
    have eq: "set S = zantema_srs (set (lr # P))"
      using IH(1) singleton zantema_srs_insert[of lr "set P"] by (simp add: S)
    have shapes: "\<forall>p \<in> set (lr # P).
        zantema_productive_pair p \<or> zantema_transfer_pair p"
      using productive IH(2) by simp
    show ?thesis using eq shapes by blast
  qed
qed

lemma zantema_encode_productive:
  assumes lr: "lr = (Fun f [Var x, unary_term lhs (Var y)],
                      Fun f [unary_term rhs (Var x), Var y])"
  shows "zantema_encode z (fst lr \<cdot> \<sigma>) =
         unary_term (rev (unary_prefix (\<sigma> x)) @ lhs @ unary_prefix (\<sigma> y)) (Var z)"
    and "zantema_encode z (snd lr \<cdot> \<sigma>) =
         unary_term (rev (unary_prefix (\<sigma> x)) @ rev rhs @ unary_prefix (\<sigma> y)) (Var z)"
  using lr by (auto simp: zantema_encode_def rev_append)

lemma zantema_encode_transfer:
  assumes lr: "lr = (Fun f [Fun a [Var x], Var y],
                      Fun f [Var x, Fun a [Var y]])"
  shows "zantema_encode z (fst lr \<cdot> \<sigma>) = zantema_encode z (snd lr \<cdot> \<sigma>)"
    and "zantema_left_depth (fst lr \<cdot> \<sigma>) > zantema_left_depth (snd lr \<cdot> \<sigma>)"
  using lr by (auto simp: zantema_encode_def zantema_left_depth_def)

fun unary_ctxt :: "'f list \<Rightarrow> ('f, 'v) ctxt" where
  "unary_ctxt [] = \<box>"
| "unary_ctxt (f # fs) = More f [] (unary_ctxt fs) []"

lemma unary_ctxt_apply[simp]:
  "(unary_ctxt fs)\<langle>t\<rangle> = unary_term fs t"
  by (induct fs) auto

lemma zantema_productive_step:
  assumes mem: "lr \<in> P"
    and lr: "lr = (Fun f [Var x, unary_term lhs (Var y)],
                    Fun f [unary_term rhs (Var x), Var y])"
    and xy: "x \<noteq> y" and lhs: "lhs \<noteq> []" and rhs: "rhs \<noteq> []"
  shows "(zantema_encode z (fst lr \<cdot> \<sigma>),
          zantema_encode z (snd lr \<cdot> \<sigma>)) \<in> rstep (zantema_srs P)"
proof -
  let ?p = "rev (unary_prefix (\<sigma> x))"
  let ?tail = "unary_term (unary_prefix (\<sigma> y)) (Var z)"
  let ?tau = "\<lambda>v. if v = x then ?tail else Var v"
  have rule: "(unary_term lhs (Var x), unary_term (rev rhs) (Var x))
      \<in> zantema_srs P"
    unfolding zantema_srs_def using mem lr xy lhs rhs by blast
  have step: "((unary_ctxt ?p)\<langle>unary_term lhs (Var x) \<cdot> ?tau\<rangle>,
               (unary_ctxt ?p)\<langle>unary_term (rev rhs) (Var x) \<cdot> ?tau\<rangle>)
      \<in> rstep (zantema_srs P)"
    by (rule rstepI[OF rule, of _ "unary_ctxt ?p" ?tau]) auto
  show ?thesis
    using step zantema_encode_productive[OF lr, of z \<sigma>]
    by simp
qed

lemma zantema_subst_step_measure:
  assumes shape: "\<And>lr. lr \<in> P \<Longrightarrow>
      zantema_productive_pair lr \<or> zantema_transfer_pair lr"
    and step: "(s, t) \<in> subst.closure P"
  shows "((zantema_encode z s, zantema_left_depth s),
          (zantema_encode z t, zantema_left_depth t))
      \<in> lex_two (rstep (zantema_srs P)) Id {(m,n). m > n}"
proof -
  from step obtain l r \<sigma> where st: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>"
    and lr: "(l,r) \<in> P"
    by (auto elim: subst.closure.cases)
  from shape[OF lr] show ?thesis
  proof
    assume "zantema_productive_pair (l,r)"
    then obtain f x y lhs rhs where
      xy: "x \<noteq> y" and lhs: "lhs \<noteq> []" and rhs: "rhs \<noteq> []"
      and pair: "(l,r) = (Fun f [Var x, unary_term lhs (Var y)],
                          Fun f [unary_term rhs (Var x), Var y])"
      unfolding zantema_productive_pair_def by blast
    from zantema_productive_step[OF lr pair xy lhs rhs, of z \<sigma>]
    show ?thesis unfolding st by simp
  next
    assume "zantema_transfer_pair (l,r)"
    then obtain f a x y where
      pair: "(l,r) = (Fun f [Fun a [Var x], Var y],
                       Fun f [Var x, Fun a [Var y]])"
      unfolding zantema_transfer_pair_def by blast
    have enc: "zantema_encode z (l \<cdot> \<sigma>) = zantema_encode z (r \<cdot> \<sigma>)"
      and depth: "zantema_left_depth (l \<cdot> \<sigma>) > zantema_left_depth (r \<cdot> \<sigma>)"
      using pair by (auto simp: zantema_encode_def zantema_left_depth_def)
    show ?thesis unfolding st using enc depth by simp
  qed
qed

theorem zantema_qdp_to_srs_sound:
  assumes SN: "SN (rstep (zantema_srs P))"
    and shape: "\<And>lr. lr \<in> P \<Longrightarrow>
      zantema_productive_pair lr \<or> zantema_transfer_pair lr"
  shows "finite_dpp (nfs, m, P, {}, {}, {}, {})"
proof -
  have compat: "Id O rstep (zantema_srs P) \<subseteq> rstep (zantema_srs P)"
    by auto
  have nat_SN: "SN {(m,n::nat). n < m}"
    using SN_nat_gt by simp
  have lex_SN:
    "SN (lex_two (rstep (zantema_srs P)) Id {(m,n::nat). m > n})"
    using Lexicographic_Extension.lex_two[OF compat SN nat_SN] .
  have measured_SN:
    "SN (inv_image
      (lex_two (rstep (zantema_srs P)) Id {(m,n). m > n})
      (\<lambda>t. (zantema_encode undefined t, zantema_left_depth t)))"
    by (rule SN_inv_image[OF lex_SN])
  have pair_SN: "SN (subst.closure P)"
  proof (rule SN_subset[OF measured_SN])
    show "subst.closure P \<subseteq>
      inv_image
        (lex_two (rstep (zantema_srs P)) Id {(m,n::nat). m > n})
        (\<lambda>t. (zantema_encode undefined t, zantema_left_depth t))"
    proof
      fix st
      assume st: "st \<in> subst.closure P"
      obtain s t where pair: "st = (s,t)" by (cases st) auto
      have measured:
        "((zantema_encode undefined s, zantema_left_depth s),
          (zantema_encode undefined t, zantema_left_depth t))
          \<in> lex_two (rstep (zantema_srs P)) Id {(m,n::nat). m > n}"
        by (rule zantema_subst_step_measure[OF shape]) (use st pair in auto)
      show "st \<in> inv_image
        (lex_two (rstep (zantema_srs P)) Id {(m,n::nat). m > n})
        (\<lambda>t. (zantema_encode undefined t, zantema_left_depth t))"
        unfolding pair inv_image_def using measured by simp
    qed
  qed
  have restricted_SN:
    "SN (subst.closure P \<inter> {(s,t). m \<longrightarrow> SN_on (rstep {}) {t}})"
    by (rule SN_subset[OF pair_SN]) auto
  show ?thesis
    using restricted_SN finite_dpp_iff_SN_rel[of nfs m P "{}"] by simp
qed

theorem zantema_qdp_to_srs_impl_sound:
  assumes trans: "zantema_transform_impl Ps = Some S"
    and SN: "SN (rstep (set S))"
  shows "finite_dpp (nfs, m, set Ps, {}, {}, {}, {})"
proof -
  from zantema_transform_impl_sound[OF trans] have
    eq: "set S = zantema_srs (set Ps)"
    and shape: "\<And>lr. lr \<in> set Ps \<Longrightarrow>
      zantema_productive_pair lr \<or> zantema_transfer_pair lr"
    by auto
  show ?thesis
    by (rule zantema_qdp_to_srs_sound[OF SN[unfolded eq] shape])
qed

end
