theory Discrete_log imports 
  CryptHOL.CryptHOL
begin 

locale dis_log = 
  fixes \<G> :: "'grp cyclic_group" (structure)
begin

type_synonym 'grp' dislog_adv = "'grp' \<Rightarrow> nat spmf"

definition dis_log :: "'grp dislog_adv \<Rightarrow> bool spmf"
where "dis_log \<A> = TRY do {
  x \<leftarrow> sample_uniform (Coset.order \<G>);
  let h = \<^bold>g (^) x; 
  x'\<leftarrow> \<A> h;
  return_spmf (x = x')} ELSE return_spmf False"

definition advantage :: "'grp dislog_adv \<Rightarrow> real"
where "advantage \<A> \<equiv> spmf (dis_log \<A>) True" 

lemma lossless_dis_log: "\<lbrakk>0 < order \<G>; \<forall> h. lossless_spmf (\<A> h)\<rbrakk> \<Longrightarrow> lossless_spmf (dis_log \<A>)"
by(auto simp add:  dis_log_def)

end 

end
