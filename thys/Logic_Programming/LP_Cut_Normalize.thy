theory LP_Cut_Normalize
  imports LP_Cut_Refresh
begin

text \<open>Use the existing verified equation normalizer on cut goals without
turning their scope markers into unification terms. The tags are disjoint from
source symbols, and decoding rejects malformed payload arities.\<close>

datatype lp_cut_tag = LPCAtomTag | LPCCutTag nat | LPCTrueTag | LPCFailTag
  | LPCMetaTag | LPCExpandTag nat | LPCUnifyTag

fun lp_cut_encode where
  "lp_cut_encode (LPCAtom a) = (LPCAtomTag,[a])"
| "lp_cut_encode (LPCCut m) = (LPCCutTag m,[])"
| "lp_cut_encode LPCTrue = (LPCTrueTag,[])"
| "lp_cut_encode LPCFail = (LPCFailTag,[])"
| "lp_cut_encode (LPCMeta a) = (LPCMetaTag,[a])"
| "lp_cut_encode (LPCExpand a m) = (LPCExpandTag m,[a])"
| "lp_cut_encode (LPCUnify a b) = (LPCUnifyTag,[a,b])"

fun lp_cut_decode where
  "lp_cut_decode (LPCAtomTag,[a]) = Some (LPCAtom a)"
| "lp_cut_decode (LPCCutTag m,[]) = Some (LPCCut m)"
| "lp_cut_decode (LPCTrueTag,[]) = Some LPCTrue"
| "lp_cut_decode (LPCFailTag,[]) = Some LPCFail"
| "lp_cut_decode (LPCMetaTag,[a]) = Some (LPCMeta a)"
| "lp_cut_decode (LPCExpandTag m,[a]) = Some (LPCExpand a m)"
| "lp_cut_decode (LPCUnifyTag,[a,b]) = Some (LPCUnify a b)"
| "lp_cut_decode _ = None"

fun lp_cut_decode_list where
  "lp_cut_decode_list [] = Some []"
| "lp_cut_decode_list (a#as) =
    (case lp_cut_decode a of None \<Rightarrow> None | Some g \<Rightarrow>
      map_option ((#) g) (lp_cut_decode_list as))"

lemma lp_cut_decode_encode[simp]: "lp_cut_decode (lp_cut_encode g) = Some g"
  by (cases g) simp_all

lemma lp_cut_encode_decode:
  "lp_cut_decode a = Some g \<Longrightarrow> lp_cut_encode g = a"
  by (induct a rule: lp_cut_decode.induct) auto

lemma lp_cut_encode_inj: "inj lp_cut_encode"
  by (rule injI) (metis lp_cut_decode_encode option.inject)

lemma lp_cut_decode_list_encode:
  "lp_cut_decode_list as = Some gs \<Longrightarrow> map lp_cut_encode gs = as"
  by (induct as arbitrary: gs) (auto split: option.splits simp: lp_cut_encode_decode)

lemma lp_cut_encode_map:
  "lp_cut_encode (lp_cut_map f g) = (fst (lp_cut_encode g), map f (snd (lp_cut_encode g)))"
  by (cases g) simp_all

definition lp_cut_normalize where
  "lp_cut_normalize fuel es gs =
    (case lp_normalize_goals fuel es (map lp_cut_encode gs) of
      None \<Rightarrow> None | Some None \<Rightarrow> Some None
      | Some (Some hs) \<Rightarrow> map_option Some (lp_cut_decode_list hs))"

theorem lp_cut_normalize_success:
  assumes checked: "lp_cut_normalize fuel es gs = Some (Some hs)"
    and equations: "lp_equations es \<eta>"
  shows "map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) hs =
    map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs"
proof -
  obtain payload where normalized:
      "lp_normalize_goals fuel es (map lp_cut_encode gs) = Some (Some payload)"
    and decoded: "lp_cut_decode_list payload = Some hs"
    using checked by (auto simp: lp_cut_normalize_def split: option.splits)
  have encoded: "map lp_cut_encode hs = payload"
    by (rule lp_cut_decode_list_encode[OF decoded])
  have evaluated: "map (\<lambda>a. lp_atom_eval a \<eta>) (map lp_cut_encode hs) =
      map (\<lambda>a. lp_atom_eval a \<eta>) (map lp_cut_encode gs)"
    using lp_normalize_goals_sound[OF normalized equations] encoded by simp
  have "map lp_cut_encode (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) hs) =
      map lp_cut_encode (map (lp_cut_map (\<lambda>t. lp_ieval t \<eta>)) gs)"
    using evaluated by (simp add: map_map o_def lp_cut_encode_map lp_atom_eval_def)
  then show ?thesis by (simp only: inj_map_eq_map[OF lp_cut_encode_inj])
qed

theorem lp_cut_normalize_failure:
  assumes "lp_cut_normalize fuel es gs = Some None"
  shows "\<not>lp_equations es \<eta>"
proof
  assume equations: "lp_equations es \<eta>"
  have normalized: "lp_normalize_goals fuel es (map lp_cut_encode gs) = Some None"
    using assms by (auto simp: lp_cut_normalize_def split: option.splits)
  show False using lp_normalize_goals_sound[OF normalized equations] by simp
qed

end
