theory LP_Cut_Domain_Joint_Free_Check
 imports LP_Cut_Domain_Return_Free_Link
begin

context cut_runtime_domain
begin

lemma joint_free_valid_sound:
  assumes valid: "lpc_joint_free_valid G F a gs h bs s r C k"
    and mgu: "mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
    and bounds: "2 * k \<le> l"
  shows "lpc_free_knowledge (set (map (\<lambda>p. lp_prefix (if fst p then l else k) (snd p)) C))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  let ?value="\<lambda>p. if fst p then rho (snd p) else lp_isubst (eta (snd p)) sigma"
  let ?name="\<lambda>p. lp_prefix (if fst p then l else k) (snd p)"
  have vars: "vars_term a \<subseteq> set G\<union>set F" and same: "\<forall>x\<in>set G\<inter>vars_term a. s x=Var x"
    and eq: "a\<cdot>s=h\<cdot>r" using valid by (auto simp: lpc_joint_free_valid_def)
  have head: "x\<in>vars_term h \<union> (\<Union>g\<in>set bs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)" if "(True,x)\<in>set C" for x
    using valid that by (auto simp: lpc_joint_free_valid_def list_ex_iff)
  have cont: "x\<in>set F \<inter> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)" if "(False,x)\<in>set C" for x
    using valid that by (auto simp: lpc_joint_free_valid_def list_ex_iff)
  have images: "\<forall>p\<in>set C. \<exists>v. (if fst p then r (snd p) else s (snd p))=Var v \<and> v\<notin>set G"
  proof (intro ballI)
    fix p assume p: "p\<in>set C"
    have image: "(case (if fst p then r (snd p) else s (snd p)) of Var v \<Rightarrow> v\<notin>set G | _ \<Rightarrow> False)"
      using valid p unfolding lpc_joint_free_valid_def by blast
    show "\<exists>v. (if fst p then r (snd p) else s (snd p))=Var v \<and> v\<notin>set G"
      using image by (cases "if fst p then r (snd p) else s (snd p)") auto
  qed
  have inj: "inj_on (\<lambda>p. if fst p then r (snd p) else s (snd p)) (set C)"
    using valid by (auto simp: lpc_joint_free_valid_def distinct_map)
  have known: "(\<forall>p\<in>set C. \<exists>v. ?value p=LPIVar v) \<and> inj_on ?value (set C)"
    by (rule joint_free_block[OF mgu vars ground free same eq head cont images inj])
  have env: "lp_cut_resolution_env k l eta sigma rho (?name p)=?value p" if p: "p\<in>set C" for p
  proof (cases p)
    case (Pair b x)
    show ?thesis
    proof (cases b)
      case True then show ?thesis by (simp add: Pair lp_cut_resolution_env_def lp_prefix_def)
    next
      case False
      have short: "length x<k" using valid p False Pair by (auto simp: lpc_joint_free_valid_def)
      have upper: "\<not> l\<le>k+length x" using short bounds by arith
      show ?thesis by (simp add: Pair False lp_cut_resolution_env_def lp_prefix_def upper)
    qed
  qed
  have variable: "\<forall>x\<in>set (map ?name C). \<exists>v. lp_cut_resolution_env k l eta sigma rho x=LPIVar v"
    using conjunct1[OF known] env by auto
  have injective: "inj_on (lp_cut_resolution_env k l eta sigma rho) (set (map ?name C))"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>set (map ?name C)" and y: "y\<in>set (map ?name C)"
      and eq': "lp_cut_resolution_env k l eta sigma rho x=lp_cut_resolution_env k l eta sigma rho y"
    obtain p q where p: "p\<in>set C" "x=?name p" and q: "q\<in>set C" "y=?name q" using x y by auto
    have val_eq: "?value p=?value q" using eq' env[OF p(1)] env[OF q(1)] p(2) q(2) by simp
    have "p=q" by (rule inj_onD[OF conjunct2[OF known] val_eq p(1) q(1)])
    then show "x=y" using p q by simp
  qed
  show ?thesis using variable injective by (simp add: lpc_free_knowledge_def)
qed


lemma joint_resolution_free_sound:
  assumes mgu: "mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
    and ground: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and free: "lpc_free_knowledge (set F) eta"
    and bounds: "2 * k \<le> l"
  shows "lpc_free_knowledge (set (lpc_joint_resolution_free fuel F G a gs h bs k l))
    (lp_cut_resolution_env k l eta sigma rho)"
proof -
  have empty: "lpc_free_knowledge {} (lp_cut_resolution_env k l eta sigma rho)"
    by (simp add: lpc_free_knowledge_def)
  let ?p="Suc (fold max (map length (vars_term_list a)) 0)"
  let ?h="h\<cdot>(\<lambda>x. Var (lp_prefix ?p x))"
  let ?V="sorted_list_of_set (vars_term a \<union> vars_term ?h)"
  let ?N="lp_cut_normalize fuel [(?h,a)] (map (\<lambda>x. LPCAtom (Var x)) ?V)"
  show ?thesis
  proof (cases ?N)
    case None then show ?thesis by (simp only: lpc_joint_resolution_free_def Let_def option.simps list.set empty)
  next
    case (Some opt)
    note outer=Some
    show ?thesis
    proof (cases opt)
      case None then show ?thesis by (simp only: lpc_joint_resolution_free_def Let_def outer option.simps list.set empty)
    next
      case (Some payload)
      let ?s="lpc_mgu_substitution ?V (map lpc_free_goal_term payload)"
      let ?r="\<lambda>x. ?s (lp_prefix ?p x)"
      let ?C="lpc_joint_free_candidates G F gs h bs ?s ?r k"
      show ?thesis
      proof (cases "lpc_joint_free_valid G F a gs h bs ?s ?r ?C k")
        case False then show ?thesis by (simp only: lpc_joint_resolution_free_def Let_def outer Some option.simps if_False list.set empty)
      next
        case True
        have known: "lpc_free_knowledge (set (map (\<lambda>p. lp_prefix (if fst p then l else k) (snd p)) ?C))
          (lp_cut_resolution_env k l eta sigma rho)"
          by (rule joint_free_valid_sound[OF True mgu ground free bounds])
        show ?thesis using known by (simp only: lpc_joint_resolution_free_def Let_def outer Some option.simps if_P[OF True])
      qed
    qed
  qed
qed


end
end
