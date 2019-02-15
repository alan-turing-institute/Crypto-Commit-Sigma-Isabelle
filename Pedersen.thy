theory Pedersen imports
  Abstract_Commitment
  "HOL-Number_Theory.Cong"
  CryptHOL.CryptHOL
  Cyclic_Group_Ext
  Discrete_log
  GCD
begin

locale pedersen_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
   assumes finite_group: "finite (carrier \<G>)"
  and order_gt_0: "order \<G> > 0"
begin

type_synonym 'grp' ck = "'grp'"
type_synonym 'grp' vk = "'grp'"
type_synonym plain = "nat"
type_synonym 'grp' commit = "'grp'"
type_synonym opening = "nat"


definition key_gen :: "('grp ck \<times> 'grp vk) spmf"
where 
  "key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g (^) x;
    return_spmf (h, h) 
  }" 

definition commit :: "'grp ck \<Rightarrow> plain \<Rightarrow> ('grp commit \<times> opening) spmf"
where 
  "commit pub_key m = do {
    d :: nat \<leftarrow> sample_uniform (order \<G>);
    let c = ((\<^bold>g (^) d) \<otimes> (pub_key (^) m));
    return_spmf (c,d) 
  }"

definition verify :: "'grp vk \<Rightarrow> plain \<Rightarrow> 'grp commit \<Rightarrow> opening \<Rightarrow> bool spmf"
where 
  "verify v_key m c d = do {
    let c' = (\<^bold>g (^) d \<otimes>  v_key (^) m);
    return_spmf (c = c') 
  }"

definition valid_msg :: "plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> msg \<in> {..<order \<G>}"

definition \<A>_cond :: "'grp commit \<Rightarrow> plain \<Rightarrow> opening \<Rightarrow> plain \<Rightarrow> opening \<Rightarrow> bool"
  where "\<A>_cond c m d m' d' = (m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1))"

definition dis_log_\<A> :: "('grp ck, plain, 'grp commit, opening) bind_adv \<Rightarrow> 'grp ck \<Rightarrow> nat spmf"
where "dis_log_\<A> \<A> h = do {
  (c, m, d, m', d') \<leftarrow> \<A> h;
  _ :: unit \<leftarrow> assert_spmf (m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1));
  _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g (^) d \<otimes> h (^) m \<and> c = \<^bold>g (^) d' \<otimes> h (^) m'); 
  return_spmf  (nat ((int d' - int d) * (fst (bezw (m - m') (order \<G>))) mod order \<G>))}"
    
sublocale abstract_commitment: abstract_commitment key_gen commit verify valid_msg \<A>_cond .
sublocale discrete_log: dis_log .

end

locale pedersen = pedersen_base + cyclic_group \<G> +
 assumes finite_group: "finite (carrier \<G>)"
begin 

lemma inverse: assumes "gcd (nat (int m - int m')) (order \<G>) = 1" and m_ge_m': "m > m'"
  shows "[(int m - int m') * (fst (bezw (nat (int m - int m')) (order \<G>))) = 1] (mod order \<G>)"
proof-
  have 1: "int m - int m' = int (m - m')" using m_ge_m' by simp
  have 2: "fst (bezw  (nat (int m - int m')) (order \<G>)) * int (m - m') + snd (bezw (nat (int m - int m')) (order \<G>)) * int (order \<G>) = 1" 
    using bezw_aux assms int_minus by presburger 
  hence 3: "(fst (bezw  (nat (int m - int m')) (order \<G>)) * int (m - m') + snd (bezw (nat (int m - int m')) (order \<G>)) * int (order \<G>)) mod (order \<G>) = 1 mod (order \<G>)" 
    by (simp add: zmod_int)
  hence 4: "(fst (bezw (nat (int m - int m')) (order \<G>)) * int  (m - m')) mod (order \<G>) = 1 mod (order \<G>)"
    by simp 
  hence 5:  "[(fst (bezw (nat (int m - int m')) (order \<G>))) *(int m - int m')  = 1] (mod order \<G>)" 
    using 1 2 3 cong_int_def by auto
  then show ?thesis by(simp add: mult.commute) 
qed

lemma mod_one_cancel: assumes "[int y * z * x = y' * x] (mod order \<G>)" and "[z * x = 1] (mod order \<G>)"
  shows "[int y = y' * x] (mod order \<G>)"
    using assms by (metis ab_semigroup_mult_class.mult_ac(1) cong_refl_int cong_scalar2_int cong_sym_int cong_trans_int mult.left_neutral semiring_normalization_rules(7))

lemma dis_log_break:
  fixes d d' m m' :: nat
  assumes c: "c = \<^bold>g (^) d \<otimes> (\<^bold>g (^) y) (^) m"
    and c': "c = \<^bold>g (^) d' \<otimes> (\<^bold>g (^) y) (^) m'"
    and y_less_order: "y < order \<G>"
    and gcd: "gcd (m - m') (order \<G>) = 1"
    and m_ge_m': "m > m'"
    and mm': "\<not> [m = m'] (mod order \<G>)"
  shows "y = nat ((int d' - int d) * (fst (bezw (m - m') (order \<G>))) mod order \<G>)" 
proof -
  have "\<^bold>g (^) (d + y * m) = \<^bold>g (^) (d' + y * m')" using c c' by (simp add: nat_pow_mult nat_pow_pow)
  hence "[d + y * m = d' + y * m'] (mod order \<G>)" by(simp add: pow_generator_eq_iff_cong finite_group)
  hence "[int d + int y * int m = int d' + int y * int m'] (mod order \<G>)" 
    by(simp add: transfer_int_nat_cong[symmetric])
  from cong_diff_int[OF this cong_refl_int, of "int d + int y * int m'"]
  have "[int y * int (m - m') = int d' - int d] (mod order \<G>)" using m_ge_m'
    by(simp add: int_distrib of_nat_diff)
  hence "[int y * int (m - m') * (fst (bezw (m - m') (order \<G>))) = (int d' - int d) * (fst (bezw (m - m') (order \<G>)))] (mod order \<G>)"
    by (simp add: cong_scalar_int)
  also have "int y * int (m - m') * (fst (bezw (m - m') (order \<G>))) = int y * (int (m - m') * (fst (bezw (m - m') (order \<G>))))"
    by simp
  also have "\<dots> = int y * (1 - snd (bezw (m - m') (order \<G>)) * order \<G>)"
    using bezw_aux[of "m - m'" "order \<G>"] gcd by(simp add: mult_ac)
  also have "[\<dots> = int y] (mod order \<G>)"
    by(simp add: right_diff_distrib cong_iff_lin_int)
  finally (cong_trans_int[OF cong_sym_eq_int[THEN iffD2]])
  have "[int y = (int d' - int d) * (fst (bezw (m - m') (order \<G>)))] (mod order \<G>)" by(simp add: cong_sym_eq_int)
  hence "int y mod order \<G> = (int d' - int d) * (fst (bezw (m - m') (order \<G>))) mod order \<G>" 
    using cong_int_def by blast
  hence "y mod order \<G> = (int d' - int d) * (fst (bezw (m - m') (order \<G>))) mod order \<G>" 
    by (simp add: zmod_int)
  then show ?thesis using y_less_order by simp
qed

lemma set_spmf_samp_uni [simp]: "set_spmf (sample_uniform (order \<G>)) = {x. x < order \<G>}"
  by(auto simp add: sample_uniform_def)

lemma correct:
  shows "spmf (abstract_commitment.correct_game m) True  = 1" 
  using finite_group order_gt_0_iff_finite  
  apply(simp add: abstract_commitment.correct_game_def Let_def commit_def verify_def)
    by(simp add: key_gen_def Let_def bind_spmf_const cong: bind_spmf_cong_simp)

theorem abstract_correct:
  shows "abstract_commitment.correct m"
  unfolding abstract_commitment.correct_def using correct by simp

lemma perfect_hiding:
  shows "spmf (abstract_commitment.hiding_game \<A>) True = 1/2"
  including monad_normalisation
proof -
  obtain \<A>1 \<A>2 where [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  note [simp] =  finite_group order_gt_0_iff_finite
  have "abstract_commitment.hiding_game (\<A>1, \<A>2) = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    (c,d) \<leftarrow> commit ck (if b then m0 else m1);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: abstract_commitment.hiding_game_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g (^) x;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
     b \<leftarrow> coin_spmf; 
    d :: nat \<leftarrow> sample_uniform (order \<G>);
    let c = ((\<^bold>g (^) d) \<otimes> (h (^) (if b then m0 else m1)));
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: commit_def key_gen_def Let_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g (^) x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    z \<leftarrow> map_spmf (\<lambda>z.  \<^bold>g (^) z \<otimes> (h (^) (if b then m0 else m1))) (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
      by(simp add: bind_map_spmf o_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g (^) x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    z \<leftarrow> map_spmf (\<lambda>z.  \<^bold>g (^) z) (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
      by(clarsimp simp add: Let_def sample_uniform_one_time_pad)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g (^) x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    z \<leftarrow> map_spmf (\<lambda>z.  \<^bold>g (^) z)  (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    map_spmf(op = guess) coin_spmf} ELSE coin_spmf"
      by(simp add: map_spmf_conv_bind_spmf)
  also have "... = coin_spmf"
     by(auto simp add: map_eq_const_coin_spmf try_bind_spmf_lossless2' map_eq_const_coin_spmf Let_def split_def bind_spmf_const try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
  ultimately show ?thesis by(simp add: spmf_of_set)
qed

theorem abstract_perfect_hiding: 
  shows "abstract_commitment.perfect_hiding \<A>"
  using perfect_hiding abstract_commitment.perfect_hiding_def by blast

lemma bind_game_eq_dis_log:
  shows "abstract_commitment.bind_game \<A> = discrete_log.dis_log (dis_log_\<A> \<A>)"
proof-
  have "abstract_commitment.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1)); 
    b \<leftarrow> verify vk m c d;
    b' \<leftarrow> verify vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: abstract_commitment.bind_game_def \<A>_cond_def) 
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (Coset.order \<G>);
    (c, m, d, m', d') \<leftarrow> \<A> (\<^bold>g (^) x);
    _ :: unit \<leftarrow> assert_spmf (m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1)); 
    _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g (^) d \<otimes>  (\<^bold>g (^) x) (^) m \<and> c = \<^bold>g (^) d' \<otimes> (\<^bold>g (^) x) (^) m');
    return_spmf True} ELSE return_spmf False" 
      by(simp add: verify_def key_gen_def Let_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    (c, m, d, m', d') \<leftarrow> \<A> (\<^bold>g (^) x);
    _ :: unit \<leftarrow> assert_spmf (m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1)); 
    _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g (^) d \<otimes>  (\<^bold>g (^) x) (^) m \<and> c = \<^bold>g (^) d' \<otimes> (\<^bold>g (^) x) (^) m');
    return_spmf (x = nat ((int d' - int d) * (fst (bezw (m - m') (order \<G>))) mod order \<G>))} ELSE return_spmf False" 
    apply(intro try_spmf_cong)
    apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
    apply(rule dis_log_break)
    by auto
  ultimately show ?thesis by(simp add: discrete_log.dis_log_def dis_log_\<A>_def Let_def split_def cong: bind_spmf_cong_simp)
qed

theorem pedersen_bind: "abstract_commitment.bind_advantage \<A> = discrete_log.advantage (dis_log_\<A> \<A>)"
  using bind_game_eq_dis_log unfolding abstract_commitment.bind_advantage_def discrete_log.advantage_def 
  by simp

end

locale pedersen_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
  assumes pedersen: "\<And>\<eta>. pedersen (\<G> \<eta>)"
begin
  
sublocale pedersen "\<G> \<eta>" for \<eta> by(simp add: pedersen)

theorem pedersen_correct: 
 shows "abstract_commitment.correct n m"
  using abstract_correct by simp

theorem pedersen_perfect_hiding:
  assumes lossless_\<A>: "abstract_commitment.lossless (\<A> n)" 
  shows "abstract_commitment.perfect_hiding n (\<A> n)"
    by (simp add: lossless_\<A> abstract_perfect_hiding)

theorem pedersen_binding:
  shows "abstract_commitment.bind_advantage n (\<A> n) = discrete_log.advantage n (dis_log_\<A> n (\<A> n))"
  using pedersen_bind by(simp)

theorem "negligible (\<lambda> n. abstract_commitment.bind_advantage n (\<A> n)) \<longleftrightarrow> negligible (\<lambda> n. discrete_log.advantage n (dis_log_\<A> n (\<A> n)))" 
  by(simp add: pedersen_binding)

end

end
