theory LP_Return_Shape_Facts
  imports LP_Return_Shapes
begin

text \<open>Decompose a known return shape along a finite source pattern.
None means that this pattern cannot have the assumed shape. Exhausted fuel or
ambiguous productions retain no additional facts; neither case establishes an
impossible branch. These observations will be used to check helper contracts,
not to assume them.\<close>

fun lp_return_merge_facts where
  "lp_return_merge_facts [] = Some []"
| "lp_return_merge_facts (None#rest) = None"
| "lp_return_merge_facts (Some facts#rest) =
    map_option (append facts) (lp_return_merge_facts rest)"

fun lp_return_shape_facts where
  "lp_return_shape_facts 0 G shape t = Some []"
| "lp_return_shape_facts (Suc fuel) G LPReturnAny t = Some []"
| "lp_return_shape_facts (Suc fuel) G LPReturnGround t =
    Some (map (Pair LPReturnGround) (vars_term_list t))"
| "lp_return_shape_facts (Suc fuel) G (LPReturnShape i) (Var x) =
    Some [(LPReturnShape i,x)]"
| "lp_return_shape_facts (Suc fuel) G (LPReturnShape i) (Fun f ts) =
    (if i<length G then
      (case filter (\<lambda>(g,shapes). f=g \<and> length shapes=length ts) (G!i) of
        [] \<Rightarrow> None
      | [(_,shapes)] \<Rightarrow> lp_return_merge_facts
          (map (\<lambda>j. lp_return_shape_facts fuel G (shapes!j) (ts!j)) [0..<length ts])
      | _ \<Rightarrow> Some [])
     else None)"

declare lp_return_shape_facts.simps[code del]
lemma lp_return_shape_facts_code[code]:
  "lp_return_shape_facts fuel G shape t =
    (if fuel=0 then Some [] else
      case shape of LPReturnAny \<Rightarrow> Some []
      | LPReturnGround \<Rightarrow> Some (map (Pair LPReturnGround) (vars_term_list t))
      | LPReturnShape i \<Rightarrow> (case t of Var x \<Rightarrow> Some [(LPReturnShape i,x)]
        | Fun f ts \<Rightarrow> (if i<length G then
          (case filter (\<lambda>(g,shapes). f=g \<and> length shapes=length ts) (G!i) of
            [] \<Rightarrow> None
          | [(_,shapes)] \<Rightarrow> lp_return_merge_facts
              (map (\<lambda>j. lp_return_shape_facts (fuel-1) G (shapes!j) (ts!j)) [0..<length ts])
          | _ \<Rightarrow> Some []) else None)))"
  by (cases fuel; cases shape; cases t) (auto split: list.splits prod.splits)

definition lp_return_facts_valid where
  "lp_return_facts_valid G rho result =
    (case result of None \<Rightarrow> False | Some known \<Rightarrow> lp_return_shape_known G known rho)"

lemma lp_return_known_append:
  "lp_return_shape_known G (a@b) rho =
    (lp_return_shape_known G a rho \<and> lp_return_shape_known G b rho)"
  by (auto simp: lp_return_shape_known_def)

lemma lp_return_merge_facts_sound:
  "list_all (lp_return_facts_valid G rho) facts \<Longrightarrow>
   lp_return_facts_valid G rho (lp_return_merge_facts facts)"
  by (induct facts rule: lp_return_merge_facts.induct)
    (auto simp: lp_return_facts_valid_def lp_return_shape_known_def split: option.splits)

lemma lp_return_empty_facts[simp]:
  "lp_return_facts_valid G rho (Some [])"
  by (simp add: lp_return_facts_valid_def lp_return_shape_known_def)

theorem lp_return_shape_facts_sound:
  assumes held: "lp_return_shape_holds G shape (lp_ieval t rho)"
  shows "lp_return_facts_valid G rho (lp_return_shape_facts fuel G shape t)"
  using held
proof (induct fuel arbitrary: shape t)
  case 0 then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases shape)
    case LPReturnAny then show ?thesis by simp
  next
    case LPReturnGround
    then show ?thesis using Suc.prems
      by (auto simp: lp_return_facts_valid_def lp_return_shape_known_def
        lp_return_ground_exact lp_seg_ground_eval)
  next
    case (LPReturnShape i)
    show ?thesis
    proof (cases t)
      case (Var x)
      then show ?thesis using Suc.prems LPReturnShape
        by (simp add: lp_return_facts_valid_def lp_return_shape_known_def)
    next
      case (Fun f ts)
      obtain shapes where bound: "i<length G" and member: "(f,shapes)\<in>set (G!i)"
        and length: "length shapes=length ts"
        and children: "\<forall>j<length ts. lp_return_shape_holds G (shapes!j) (lp_ieval (ts!j) rho)"
        using lp_return_shape_node[OF Suc.prems[unfolded LPReturnShape Fun]] by auto
      let ?matches = "filter (\<lambda>(g,shapes). f=g \<and> length shapes=length ts) (G!i)"
      have member_match: "(f,shapes)\<in>set ?matches" using member length by simp
      show ?thesis
      proof (cases ?matches)
        case Nil then show ?thesis using member_match by simp
      next
        case (Cons first rest)
        show ?thesis
        proof (cases rest)
          case Nil
          have first: "first=(f,shapes)" using member_match Cons Nil by simp
          have valid: "list_all (lp_return_facts_valid G rho)
            (map (\<lambda>j. lp_return_shape_facts fuel G (shapes!j) (ts!j)) [0..<length ts])"
            using Suc.hyps children by (auto simp: list_all_iff)
          show ?thesis using lp_return_merge_facts_sound[OF valid]
            by (simp add: LPReturnShape Fun bound Cons Nil first)
        next
          case (Cons second more)
          then show ?thesis using \<open>?matches=first#rest\<close> bound
            by (cases first; cases second; simp add: LPReturnShape Fun)
        qed
      qed
    qed
  qed
qed


definition lp_return_shape_ground_vars where
  "lp_return_shape_ground_vars fuel G shape t = (case lp_return_shape_facts fuel G shape t of
    None \<Rightarrow> {} | Some facts \<Rightarrow> set (map snd (filter (\<lambda>(s,x). s=LPReturnGround) facts)))"

lemma lp_return_shape_ground_vars_sound:
  assumes held: "lp_return_shape_holds G shape (lp_ieval t eta)"
  shows "\<forall>x\<in>lp_return_shape_ground_vars fuel G shape t. lp_seg_ground (eta x)"
  using lp_return_shape_facts_sound[where fuel=fuel, OF held]
  by (auto simp: lp_return_shape_ground_vars_def lp_return_facts_valid_def
    lp_return_shape_known_def lp_return_ground_exact split: option.splits)

end
