theory LP_Prolog_Probe_Builtin
  imports LP_Prolog_Opaque_Probe LP_Prolog_Integer_Source
begin

definition lpp_probe_name :: "string \<Rightarrow> bool" where
  "lpp_probe_name f = (f=''1:once'' \<or> f=''1:not'' \<or> f=map char_of_nat [49,58,92,43])"

definition lpp_probe_domain ::
  "string \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm list \<Rightarrow> bool" where
  "lpp_probe_domain f ts = (lpp_probe_name f \<and>
    (\<exists>g us. ts=[LPIFun (LPCUser g) us]))"

definition lpp_probe_outcome ::
  "string \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm list \<Rightarrow>
    (string,'w) lpp_builtin_result \<Rightarrow> bool" where
  "lpp_probe_outcome f ts outcome = (lpp_probe_domain f ts \<and>
    outcome=LPPBuiltinProbe (hd ts) (f=''1:once''))"

text \<open>The supported domain has a known callable atom at its root. Its
arguments may be rational and need not be ground. Variable callables and special
control syntax require separate checked lowering; this domain does not claim
to cover them. In particular, entering a probe supplies no success or return
facts about its argument.\<close>

lemma lpp_probe_total:
  "lpp_probe_domain f ts \<Longrightarrow> \<exists>outcome. lpp_probe_outcome f ts outcome"
  by (auto simp: lpp_probe_outcome_def)

lemma lpp_probe_signatures:
  "(''1:once'',1)\<in>lpp_builtin_signature"
  "(''1:not'',1)\<in>lpp_builtin_signature"
  "(map char_of_nat [49,58,92,43],1)\<in>lpp_builtin_signature"
  by code_simp+

lemma lpp_probe_selected:
  "lpp_probe_domain f ts \<Longrightarrow> (f,length ts)\<in>lpp_builtin_signature"
  using lpp_probe_signatures
  by (auto simp: lpp_probe_domain_def lpp_probe_name_def)

lemma lpp_probe_legacy_flags:
  "lpp_var_name ''1:once'' = False"
  "lpp_identity_name ''1:once'' = False"
  "lpp_source_comparison ''1:once'' = None"
  "''1:once'' \<noteq> ''1:integer''"
  "''1:once'' \<noteq> ''2:is''"
  "lpp_var_name ''1:not'' = False"
  "lpp_identity_name ''1:not'' = False"
  "lpp_source_comparison ''1:not'' = None"
  "''1:not'' \<noteq> ''1:integer''"
  "''1:not'' \<noteq> ''2:is''"
  "lpp_var_name (map char_of_nat [49,58,92,43]) = False"
  "lpp_identity_name (map char_of_nat [49,58,92,43]) = False"
  "lpp_source_comparison (map char_of_nat [49,58,92,43]) = None"
  "(map char_of_nat [49,58,92,43]) \<noteq> ''1:integer''"
  "(map char_of_nat [49,58,92,43]) \<noteq> ''2:is''"
  by code_simp+

lemma lpp_probe_legacy_excluded:
  "lpp_integer_source_domain ''1:once'' ts = False"
  "lpp_integer_source_domain ''1:not'' ts = False"
  "lpp_integer_source_domain (map char_of_nat [49,58,92,43]) ts = False"
  by (simp only: lpp_integer_source_domain.simps lpp_probe_legacy_flags if_False option.case HOL.simp_thms)+

lemma lpp_probe_not_integer_domain:
  "lpp_probe_name f \<Longrightarrow> \<not>lpp_integer_source_domain f ts"
  using lpp_probe_legacy_excluded[of ts]
  by (auto simp only: lpp_probe_name_def)

end
