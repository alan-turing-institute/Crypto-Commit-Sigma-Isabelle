theory Uniform_Sampling_Defs imports 
  CryptHOL.CryptHOL
begin 

definition samp_uni_excl :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf"
  where "samp_uni_excl n p = spmf_of_set ({..< n} - {p})"

lemma [simp]: "set_spmf (samp_uni_excl n p) = {..< n} - {p}"
  by(simp add: samp_uni_excl_def)

definition "samp_uni_units n = spmf_of_set ({..< n} - {0})"

definition samp_uni_units_excl :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf"
  where "samp_uni_units_excl n p = spmf_of_set ({..< n} - {p} - {0})"

end