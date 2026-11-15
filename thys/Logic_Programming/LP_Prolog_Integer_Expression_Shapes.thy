theory LP_Prolog_Integer_Expression_Shapes
 imports LP_Prolog_Stable_Context
begin

text \<open>Finite return shapes can describe integer expression trees. The
existing shape semantics is inductive, including on rational runtime terms.
Neither a ground field nor an unconstrained field establishes integer evaluation.
This reuses the checked source initialization and interface transport of shapes.\<close>

fun lpp_integer_shape_production :: "string lp_cut_symbol \<times> lp_return_shape list \<Rightarrow> bool" where
  "lpp_integer_shape_production (f,[]) =
    ((Fun f [] :: (string lp_cut_symbol,string) term) = lpp_integer_term (lpp_context_literal_candidate (Fun f [] :: (string lp_cut_symbol,string) term)))"
| "lpp_integer_shape_production (f,[LPReturnShape i]) =
    (f=LPCUser ''1:prolog_data_2b'' \<or> f=LPCUser ''1:prolog_data_2d'')"
| "lpp_integer_shape_production (f,[LPReturnShape i,LPReturnShape j]) =
    (f=LPCUser ''2:prolog_data_2b'' \<or> f=LPCUser ''2:prolog_data_2d'' \<or> f=LPCUser ''2:prolog_data_2a'')"
| "lpp_integer_shape_production production = False"

definition lpp_integer_shape_grammar where
  "lpp_integer_shape_grammar G = list_all (list_all lpp_integer_shape_production) G"

fun lpp_integer_expression_shape where
  "lpp_integer_expression_shape G (LPReturnShape i) = (i<length G \<and> lpp_integer_shape_grammar G)"
| "lpp_integer_expression_shape G shape = False"

lemma lpp_integer_shape_evaluation:
  assumes shape: "lp_return_shape_holds G s t"
    and grammar: "lpp_integer_shape_grammar G"
  shows "\<forall>i. s=LPReturnShape i \<longrightarrow> (\<exists>n. lpp_integer_evaluation t n)"
  using shape
proof (induction rule: lp_return_shape_holds.induct)
  case (any t) then show ?case by simp
next
  case (ground t) then show ?case by simp
next
  case (node i f shapes ts)
  have production: "lpp_integer_shape_production (f,shapes)"
    using grammar node.hyps(1,2) by (auto simp: lpp_integer_shape_grammar_def list_all_iff dest: nth_mem)
  consider (literal) "shapes=[]" "f=LPCUser (lpp_integer_name (lpp_context_literal_candidate (Fun f [] :: (string lp_cut_symbol,string) term)))"
    | (unary) k where "shapes=[LPReturnShape k]"
        "f=LPCUser ''1:prolog_data_2b'' \<or> f=LPCUser ''1:prolog_data_2d''"
    | (binary) k l where "shapes=[LPReturnShape k,LPReturnShape l]"
        "f=LPCUser ''2:prolog_data_2b'' \<or> f=LPCUser ''2:prolog_data_2d'' \<or> f=LPCUser ''2:prolog_data_2a''"
    using production by (cases "(f,shapes)" rule: lpp_integer_shape_production.cases) (auto simp: lpp_integer_term_def)
  then show ?case
  proof cases
    case literal
    have ts: "ts=[]" using node.hyps(3) literal by simp
    have literal_value: "LPIFun f ts = lpp_integer_value (lpp_context_literal_candidate (Fun f [] :: (string lp_cut_symbol,string) term))"
      using literal ts by (simp add: lpp_integer_term_def lpp_integer_value_def)
    show ?thesis unfolding literal_value using lpp_integer_evaluation.literal by blast
  next
    case (unary k)
    obtain a where ts: "ts=[a]" using node.hyps(3) unary(1) by (auto simp: Suc_length_conv)
    obtain n where evaluated: "lpp_integer_evaluation a n"
      using node.IH[of 0] unary(1) ts by auto
    show ?thesis using evaluated unary(2) ts
      by (auto intro: lpp_integer_evaluation.positive lpp_integer_evaluation.negate)
  next
    case (binary k l)
    obtain a b where ts: "ts=[a,b]" using node.hyps(3) binary(1) by (auto simp: Suc_length_conv length_Suc_conv)
    obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
      using node.IH[of 0] node.IH[of 1] binary(1) ts by auto
    show ?thesis using left right binary(2) ts
      by (auto intro: lpp_integer_evaluation.add lpp_integer_evaluation.subtract lpp_integer_evaluation.multiply)
  qed
qed

lemma lpp_integer_expression_shape_sound:
  assumes "lpp_integer_expression_shape G shape" "lp_return_shape_holds G shape t"
  shows "\<exists>n. lpp_integer_evaluation t n"
  using assms lpp_integer_shape_evaluation[OF assms(2)]
  by (cases shape) auto

ML \<open>
val checked = [@{thm lpp_integer_expression_shape_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted integer expression shape dependency" else ();
\<close>
end
