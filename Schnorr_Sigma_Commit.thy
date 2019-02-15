theory Schnorr_Sigma_Commit imports 
  Abstract_Commitment
  Abstract_Sigma_Protocols
  Cyclic_Group_Ext
  Discrete_log
  Uniform_Sampling 
  Uniform_Sampling_Defs
begin 

locale schnorr_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes finite_group: "finite (carrier \<G>)"
    and order_gt_0: "order \<G> > 0"
    and prime_order: "prime (order \<G>)"
    and prime_field: "a < (order \<G>) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a (order \<G>)"
begin

type_synonym witness = "nat"
type_synonym rand = nat 
type_synonym 'grp' msg = "'grp'"
type_synonym response = nat
type_synonym challenge = nat
type_synonym 'grp' pub_in = "'grp'"

definition R_DL :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> bool"
  where "R_DL h w \<equiv> (h = \<^bold>g (^) w \<and> w \<noteq> 0 \<and> w < order \<G>)"

lemma lossless_samp_uni_excl: "lossless_spmf (samp_uni_excl (order \<G>) p)"
  apply(simp add: samp_uni_excl_def)
  using order_gt_0
  by (metis One_nat_def card.insert card_empty card_lessThan empty_iff finite.intros(1) less_irrefl prime_gt_1_nat prime_order subset_singletonD) 

lemma set_spmf_samp_uni [simp]: "set_spmf (sample_uniform (order \<G>)) = {x. x < order \<G>}"
  by(auto simp add: sample_uniform_def)

definition init :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> (rand \<times> 'grp msg) spmf"
  where "init h w = do {
    r \<leftarrow> sample_uniform (order \<G>);
    return_spmf (r, \<^bold>g (^) r)}"

definition "challenge = sample_uniform (order \<G>)"

definition "snd_challenge p = samp_uni_excl (order \<G>) p"

definition "response r w c = return_spmf ((w*c + r) mod (order \<G>))"

definition check :: "'grp pub_in \<Rightarrow> 'grp msg \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool spmf"
  where "check h a e z = return_spmf (a \<otimes> (h (^) e) = \<^bold>g (^) z)"

definition R2 :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> ('grp msg, challenge, response) conv_tuple spmf"
where "R2 h w = do {
  (r, a) \<leftarrow> init h w; 
  c \<leftarrow> sample_uniform (order \<G>);
  let z = (w*c + r) mod (order \<G>);
  return_spmf (a,c, z)}"

lemma "R2 h w = do {
  r \<leftarrow> sample_uniform (order \<G>);
  let (r, a) = (r, \<^bold>g (^) r); 
  c \<leftarrow> sample_uniform (order \<G>);
  let z = (w*c + r) mod (order \<G>);
  return_spmf (a,c, z)}" 
  by(simp add: R2_def init_def)

definition S2 :: "'grp \<Rightarrow> challenge \<Rightarrow> ('grp msg, challenge, response) conv_tuple spmf"
where "S2 h e = do {
  c \<leftarrow> sample_uniform (order \<G>);
  let a = \<^bold>g (^) c \<otimes> (inv (h (^) e));
  return_spmf (a, e, c)}"

definition pk_adversary :: "'grp \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> nat spmf"
  where "pk_adversary x c1 c2 = do {
    let (a, e, z) = c1;
    let (a', e', z') = c2;
    return_spmf (if e > e' then (nat ((int z - int z') * (fst (bezw (e - e') (order \<G>))) mod order \<G>)) else 
(nat ((int z' - int z) * (fst (bezw (e' - e) (order \<G>))) mod order \<G>)))}"

sublocale epsilon_protocols_base: epsilon_protocols_base init challenge snd_challenge response check R_DL S2 .

lemma R2_eq_R: "R2 h w = epsilon_protocols_base.R h w"
  unfolding  R2_def epsilon_protocols_base.R_def Let_def 
  by(simp add: challenge_def response_def)

(*use Schnorr to make commitment protocol*)

type_synonym 'grp' ck = "'grp'"
type_synonym 'grp' vk = "'grp' \<times> nat"
type_synonym plain = "nat"
type_synonym 'grp' commit = "'grp'"
type_synonym opening = "nat" (*just z, as this is the opening value as the message is set with it*)

definition gen :: "('grp ck \<times> 'grp vk) spmf" (*outputs commitment key and verify key*)
  where "gen = do {
    w \<leftarrow> sample_uniform (order \<G>);
    return_spmf (\<^bold>g (^) w, (\<^bold>g (^) w, w))}"

definition commit :: "'grp ck \<Rightarrow> plain \<Rightarrow> ('grp commit \<times> opening) spmf"
  where "commit ck e = do {
    (a, e, z) \<leftarrow> S2 ck e;
    return_spmf (a, z)}"

definition verify :: "'grp vk \<Rightarrow> plain \<Rightarrow> 'grp commit \<Rightarrow> opening \<Rightarrow> bool spmf"
  where "verify h e c z = (check (fst h) c e z)" 

definition "valid_msg m \<equiv> m < order \<G>"

definition \<A>_cond :: "'grp commit \<Rightarrow> plain \<Rightarrow> opening \<Rightarrow> plain \<Rightarrow> opening \<Rightarrow> bool"
  where "\<A>_cond c m d m' d' = (m > m' \<and> \<not> [m = m'] (mod order \<G>) \<and> (gcd (m - m') (order \<G>) = 1) \<and> c \<in> carrier \<G>)"

definition dis_log_\<A> :: "('grp ck, plain, 'grp commit, opening) bind_adv \<Rightarrow> 'grp ck \<Rightarrow> nat spmf"
where "dis_log_\<A> \<A> h = do {
  (c, e, z, e', z') \<leftarrow> \<A> h;
  _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
  _ :: unit \<leftarrow> assert_spmf (((c \<otimes> h (^) e) = \<^bold>g (^) z) \<and> (c \<otimes> h (^) e') = \<^bold>g (^) z'); 
  return_spmf  (nat ((int z - int z') * (fst (bezw (e - e') (order \<G>))) mod order \<G>))}"

sublocale abstract_commitment: abstract_commitment gen commit verify valid_msg \<A>_cond .
sublocale discrete_log: dis_log .

end

locale schnorr_sigma_protocol = schnorr_base + cyclic_group \<G>
begin

lemma complete: assumes "h = \<^bold>g (^) (w::nat)"
  shows "spmf (epsilon_protocols_base.completeness_game h w) True = 1"
proof-
  have "\<^bold>g (^) y \<otimes> (\<^bold>g (^) w) (^) e = \<^bold>g (^) (y + w * e)" for y e
    using nat_pow_pow nat_pow_mult by simp
  then show ?thesis 
    unfolding  epsilon_protocols_base.completeness_game_def 
    by(simp add: init_def challenge_def response_def check_def pow_generator_mod assms add.commute bind_spmf_const order_gt_0)
qed

lemma completeness: "epsilon_protocols_base.completeness h w"
  by(simp add: epsilon_protocols_base.completeness_def R_DL_def complete)

lemma zr: 
  assumes z: "z = (x*c + r) mod (order \<G>)" 
    and x: "x < order \<G>" 
    and c: "c < order \<G>" 
    and r: "r < order \<G>"
  shows "(z + (order \<G>)*(order \<G>) - x*c) mod (order \<G>) = r"
proof-
  have cong: "[z + (order \<G>)*(order \<G>) = x*c + r] (mod (order \<G>))" 
    by(simp add: cong_nat_def z)
  hence "[z + (order \<G>)*(order \<G>) - x*c = r] (mod (order \<G>))" 
  proof-
    have "z + (order \<G>)*(order \<G>) > x*c" 
      using x c by (simp add: mult_strict_mono trans_less_add2)
    then show ?thesis
      by (metis cong add_diff_inverse_nat cong_add_lcancel_nat less_imp_le linorder_not_le) 
  qed
  then show ?thesis
    by(simp add: cong_nat_def r)
qed

lemma h_sub:
  assumes "h = \<^bold>g (^) x" and x_not_0: "x \<noteq> 0" and x: "x < order \<G>" and z: "z < order \<G>" and c: "c < order \<G>"
  shows "\<^bold>g (^) ((z + (order \<G>)*(order \<G>) - x*c)) = \<^bold>g (^) z \<otimes> inv (h (^) c)" 
(is "?lhs = ?rhs")
proof-
  have "(z + order \<G> * order \<G> - x * c) = (z + (order \<G> * order \<G> - x * c))"
    using x c z by (simp add: less_imp_le_nat mult_le_mono) 
  then have lhs: "?lhs = \<^bold>g (^) z \<otimes> \<^bold>g (^) ((order \<G>)*(order \<G>) - x*c)" by(simp add: nat_pow_mult)
  have " \<^bold>g (^) ((order \<G>)*(order \<G>) - x*c) =  inv (h (^) c)"  
  proof-
    have "((order \<G>)*(order \<G>) - x*c) > 0" using assms
      by (simp add: mult_strict_mono)
    then have " \<^bold>g (^) ((order \<G>)*(order \<G>) - x*c) =  \<^bold>g (^) int ((order \<G>)*(order \<G>) - x*c)"
      by (simp add: int_pow_int) 
    also have "... = \<^bold>g (^) int ((order \<G>)*(order \<G>)) \<otimes> inv (\<^bold>g (^) (x*c))" 
      using int_pow_diff[of "\<^bold>g" "order \<G> * order \<G>" "x * c"]
      by (smt \<open>0 < order \<G> * order \<G> - x * c\<close> generator_closed group.int_pow_def2 group_l_invI int_minus int_pow_int l_inv_ex of_nat_less_iff zero_less_diff) 
    also have "... = \<^bold>g (^) ((order \<G>)*(order \<G>)) \<otimes> inv (\<^bold>g (^) (x*c))"
      by (metis int_pow_int) 
    also have "... = \<^bold>g (^) ((order \<G>)*(order \<G>)) \<otimes> inv ((\<^bold>g (^) x) (^) c)"
      by(simp add: nat_pow_pow)
    also have "... = \<^bold>g (^) ((order \<G>)*(order \<G>)) \<otimes> inv (h (^) c)"
      using assms by simp
    also have "... = \<one> \<otimes> inv (h (^) c)"
      using generator_pow_order
      by (metis generator_closed mult_is_0 nat_pow_0 nat_pow_pow)
    ultimately show ?thesis
      by (simp add: assms(1)) 
  qed
  then show ?thesis using lhs by simp
qed

lemma hv_zk: assumes "h = \<^bold>g (^) x" and "x \<noteq> 0" and "x < order \<G>"
  shows "epsilon_protocols_base.R h x = bind_spmf challenge (S2 h)"
  including monad_normalisation
proof-
  have "R2 h x = bind_spmf challenge (S2 h)"
  proof-
    have "R2 h x = do {
      r \<leftarrow> sample_uniform (order \<G>);
      c \<leftarrow> sample_uniform (order \<G>);
      let z = (x*c + r) mod (order \<G>);
      let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - x*c) mod (order \<G>)); 
      return_spmf (a,c,z)}"
      apply(simp add: Let_def R2_def init_def)
      using assms zr by(simp cong: bind_spmf_cong_simp)
    also have "... = do {
      c \<leftarrow> sample_uniform (order \<G>);
      z \<leftarrow> map_spmf (\<lambda> r. (x*c + r) mod (order \<G>)) (sample_uniform (order \<G>));
      let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - x*c) mod (order \<G>)); 
      return_spmf (a,c,z)}"
      by(simp add: bind_map_spmf o_def Let_def)
    also have "... = do {
      c \<leftarrow> sample_uniform (order \<G>);
      z \<leftarrow>  (sample_uniform (order \<G>));
      let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - x*c)); 
      return_spmf (a,c,z)}"
      by(simp add: samp_uni_plus_one_time_pad pow_generator_mod)
    also have "... = do {
      c \<leftarrow> sample_uniform (order \<G>);
      z \<leftarrow>  (sample_uniform (order \<G>));
      let a = \<^bold>g (^) z \<otimes> inv (h (^) c); 
      return_spmf (a,c,z)}"
      using h_sub assms by(simp cong: bind_spmf_cong_simp)
    ultimately show ?thesis 
      unfolding S2_def Let_def R2_def challenge_def by simp
  qed
  then show ?thesis using R2_eq_R by simp
qed

lemma honest_verifier_ZK: 
  shows "epsilon_protocols_base.honest_V_ZK h w"
    unfolding epsilon_protocols_base.honest_V_ZK_def
    by(auto simp add: hv_zk R_DL_def)

lemma inverse: assumes "gcd x (order \<G>) = 1" 
  shows "[x * (fst (bezw x (order \<G>))) = 1] (mod order \<G>)"
proof-
  have 2: "fst (bezw  x (order \<G>)) * x + snd (bezw x (order \<G>)) * int (order \<G>) = 1" 
    using bezw_aux assms int_minus by presburger 
  hence 3: "(fst (bezw  x (order \<G>)) * x + snd (bezw x (order \<G>)) * int (order \<G>)) mod (order \<G>) = 1 mod (order \<G>)" 
    by (simp add: zmod_int)
  hence 4: "(fst (bezw x (order \<G>)) * x) mod (order \<G>) = 1 mod (order \<G>)"
    by simp 
  hence 5:  "[(fst (bezw x (order \<G>))) * x  = 1] (mod order \<G>)" 
    using 2 3 cong_int_def by auto
  then show ?thesis by(simp add: mult.commute) 
qed

lemma witness_find:
  assumes "ya < order \<G>" and "yb < order \<G>" and "y < order \<G>" and w: "w < order \<G>" and "ya \<noteq> yb" and "w \<noteq> 0"
  shows "w = (if (ya > yb) then nat ((int ((w * ya + y) mod order \<G>) - int ((w * yb + y) mod order \<G>)) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>)) 
            else nat ((int ((w * yb + y) mod order \<G>) - int ((w * ya + y) mod order \<G>)) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>)))"
proof(cases "ya > yb")
  case True
 have gcd: "gcd (ya - yb) (order \<G>) = 1"
  proof-
    have "(ya - yb) < order \<G>" and "(ya - yb) \<noteq> 0" 
      apply(simp add: less_imp_diff_less assms True) 
      using True by simp
    then show ?thesis using prime_field by blast
  qed
  have "[w*(ya - yb)*(fst (bezw (ya - yb) (order \<G>))) = (w*ya - w*yb)*(fst (bezw (ya - yb) (order \<G>)))] (mod (order \<G>))"
    by (simp add: diff_mult_distrib2 assms cong_nat_def) 
  hence "[w*((ya - yb)*(fst (bezw (ya - yb) (order \<G>)))) = (w*ya - w*yb)*(fst (bezw (ya - yb) (order \<G>)))] (mod (order \<G>))"
    by (simp add: mult.assoc) 
  hence "[w = (w*ya - w*yb)*(fst (bezw (ya - yb) (order \<G>)))] (mod (order \<G>))"
    by (metis (no_types, hide_lams) gcd inverse[of "(ya - yb)"] cong_scalar_int cong_sym_int cong_trans_int mult.commute mult.left_neutral)  
  hence "[int w = (int w* int ya - int w* int yb)*(fst (bezw (ya - yb) (order \<G>)))] (mod (order \<G>))"
    by (simp add: True less_imp_le_nat of_nat_diff)
  hence "int w mod order \<G>  = (int w* int ya - int w* int yb)*(fst (bezw (ya - yb) (order \<G>))) mod (order \<G>)"
    using cong_int_def by blast
  hence "w mod order \<G>  = (int w* int ya - int w* int yb)*(fst (bezw (ya - yb) (order \<G>))) mod (order \<G>)"
    by (simp add: zmod_int)
  then show ?thesis using w
  proof -
    have f1: "\<forall>n na nb. int (nb + na) - int (nb + n) = int na - int n"
      by simp
    have "(int (w * ya) - int (w * yb)) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>) = int w"
      using \<open>int (w mod order \<G>) = (int w * int ya - int w * int yb) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>)\<close> w by force
    then show ?thesis
      using f1
    proof -
      have "nat ((int ((y + w * ya) mod order \<G>) - int ((y + w * yb) mod order \<G>)) * fst (bezw (if True then ya - yb else yb - ya) (order \<G>)) mod int (order \<G>)) = w"
        by (metis (no_types) \<open>(int (w * ya) - int (w * yb)) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>) = int w\<close> \<open>\<forall>n na nb. int (nb + na) - int (nb + n) = int na - int n\<close> mod_diff_left_eq mod_diff_right_eq mod_mult_cong nat_int zmod_int)
      then show ?thesis
        by (simp add: True add.commute)
    qed  
  qed 
next
  case False
  have False': "yb > ya" using False assms
    using nat_neq_iff by blast 
  have gcd: "gcd (yb - ya) (order \<G>) = 1"
  proof-
    have "(yb - ya) < order \<G>" and "(yb - ya) \<noteq> 0" 
      using less_imp_diff_less assms apply blast
      using assms(6) zero_less_diff False' by blast
    then show ?thesis using prime_field by blast
  qed
  have "[w*(yb - ya)*(fst (bezw (yb - ya) (order \<G>))) = (w*yb - w*ya)*(fst (bezw (yb - ya) (order \<G>)))] (mod (order \<G>))"
    using assms cong_nat_def
    by (simp add: diff_mult_distrib2) 
  then have "[w*((yb - ya)*(fst (bezw (yb - ya) (order \<G>)))) = (w*yb - w*ya)*(fst (bezw (yb - ya) (order \<G>)))] (mod (order \<G>))"
    by (simp add: mult.assoc) 
  then have "[w = (w*yb - w*ya)*(fst (bezw (yb - ya) (order \<G>)))] (mod (order \<G>))"
    using gcd inverse[of "(yb - ya)"]
    by (metis (no_types, hide_lams) cong_scalar_int cong_sym_int cong_trans_int mult.commute mult.left_neutral)  
  then have "[int w = (int w* int yb - int w* int ya)*(fst (bezw (yb - ya) (order \<G>)))] (mod (order \<G>))"
    by (simp add: False' less_imp_le_nat of_nat_diff)
  then have "int w mod order \<G>  = (int w* int yb - int w* int ya)*(fst (bezw (yb - ya) (order \<G>))) mod (order \<G>)"
    using cong_int_def by blast
  hence "w mod order \<G>  = (int w* int yb - int w* int ya)*(fst (bezw (yb - ya) (order \<G>))) mod (order \<G>)"
    by (simp add: zmod_int)
  then show ?thesis using w
  proof -
    have f1: "\<forall>n na nb. int (nb + na) - int (nb + n) = int na - int n"
      by simp
    have "(int (w * yb) - int (w * ya)) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>) = int w"
      using \<open>int (w mod order \<G>) = (int w * int yb - int w * int ya) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>)\<close> w by force
    then show ?thesis
      using f1
    proof -
      have "nat ((int ((y + w * yb) mod order \<G>) - int ((y + w * ya) mod order \<G>)) * fst (bezw (if True then yb - ya else ya - yb) (order \<G>)) mod int (order \<G>)) = w"
        by (metis (no_types) \<open>(int (w * yb) - int (w * ya)) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>) = int w\<close> \<open>\<forall>n na nb. int (nb + na) - int (nb + n) = int na - int n\<close> mod_diff_left_eq mod_diff_right_eq mod_mult_cong nat_int zmod_int)
      then show ?thesis
        by (simp add: False add.commute)
    qed  
  qed 
qed

lemma special_soundness:
  shows "epsilon_protocols_base.special_soundness h w"
proof-
  {assume w1: "w \<noteq> 0" and w2: "w < order \<G>"
    have "local.epsilon_protocols_base.special_soundness_game h w pk_adversary = return_spmf True"
      (is "?lhs = ?rhs")
  proof-
    have "?lhs = do {
      y \<leftarrow> sample_uniform (order \<G>);
      ya \<leftarrow> sample_uniform (order \<G>);
      yb \<leftarrow> samp_uni_excl (order \<G>) ya;
      return_spmf (w = (if (ya > yb) then nat ((int ((w * ya + y) mod order \<G>) - int ((w * yb + y) mod order \<G>)) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>)) 
          else nat ((int ((w * yb + y) mod order \<G>) - int ((w * ya + y) mod order \<G>)) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>))))}"
       unfolding local.epsilon_protocols_base.special_soundness_game_def pk_adversary_def 
       by(simp add: response_def challenge_def init_def snd_challenge_def)
    then show ?thesis 
      by(simp add: witness_find w1 w2 bind_spmf_const lossless_samp_uni_excl order_gt_0 lossless_weight_spmfD cong: bind_spmf_cong_simp)
  qed }
  then have "w \<noteq> 0 \<Longrightarrow> w < order \<G> \<Longrightarrow> spmf (local.epsilon_protocols_base.special_soundness_game h w pk_adversary) True = 1"
     by simp
  then show ?thesis unfolding epsilon_protocols_base.special_soundness_def R_DL_def by auto
qed

theorem sigma_protocol: "epsilon_protocols_base.\<Sigma>_protocol h w"
  by(simp add: epsilon_protocols_base.\<Sigma>_protocol_def completeness honest_verifier_ZK special_soundness)

end

locale schnorr_commitment = schnorr_base + cyclic_group \<G>
begin

lemma correct: "abstract_commitment.correct_game m = return_spmf True"
proof-
  have carrier: "(\<^bold>g (^) (y::nat)) (^) m \<in> carrier \<G>" for y by simp
  have "\<^bold>g (^) (ya::nat) \<otimes> inv ((\<^bold>g (^) (y::nat)) (^) m) \<otimes> (\<^bold>g (^) y) (^) m = \<^bold>g (^) ya" for ya y
  proof-
    have "\<^bold>g (^) (ya::nat) \<otimes> inv ((\<^bold>g (^) (y::nat)) (^) m) \<otimes> (\<^bold>g (^) y) (^) m = \<^bold>g (^) (ya::nat) \<otimes> (inv ((\<^bold>g (^) (y::nat)) (^) m) \<otimes> (\<^bold>g (^) y) (^) m)" 
      by (simp add: monoid.m_assoc)
    then show ?thesis by simp
  qed
  then show ?thesis 
    by(simp add: commit_def gen_def Abstract_Commitment.abstract_commitment.correct_game_def verify_def S2_def bind_spmf_const order_gt_0 check_def)
qed

lemma abstract_correct: "abstract_commitment.correct m"
  by(simp add: abstract_commitment.correct_def correct[of "m"])

lemma perfect_hiding: "abstract_commitment.hiding_game \<A> = coin_spmf"
  including monad_normalisation
proof-
  obtain \<A>1 and \<A>2 where "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  note [simp] = this order_gt_0_iff_finite finite_group try_spmf_bind_out split_def o_def spmf_of_set bind_map_spmf weight_spmf_le_1 scale_bind_spmf bind_spmf_const
    and [cong] = bind_spmf_cong_simp
  have "abstract_commitment.hiding_game (\<A>1, \<A>2) = TRY do {
  w \<leftarrow> sample_uniform (order \<G>);
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 ( \<^bold>g (^) w ,w);
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  b \<leftarrow> coin_spmf; 
  c' \<leftarrow> sample_uniform (order \<G>);
  let c = \<^bold>g (^) c' \<otimes> (inv ((\<^bold>g (^) w) (^) (if b then m0 else m1)));
  b' \<leftarrow> \<A>2 c \<sigma>;
  return_spmf (b' = b)} ELSE coin_spmf"
    by(simp add: Abstract_Commitment.abstract_commitment.hiding_game_def gen_def commit_def S2_def) 
  also have "... = TRY do {
  w \<leftarrow> sample_uniform (order \<G>);
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g (^) w, w);
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  b \<leftarrow> coin_spmf; 
  c \<leftarrow> map_spmf (\<lambda> c'. \<^bold>g (^) c' \<otimes> (inv ((\<^bold>g (^) w) (^) (if b then m0 else m1)))) (sample_uniform (order \<G>));
  b' \<leftarrow> \<A>2 c \<sigma>;
  return_spmf (b' = b)} ELSE coin_spmf"
    by(simp add: Let_def)
  also have "... = TRY do {
  w :: nat \<leftarrow> sample_uniform (order \<G>);
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g (^) w, w);
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  b :: bool \<leftarrow> coin_spmf; 
  c \<leftarrow> map_spmf (\<lambda> c'. \<^bold>g (^) c') (sample_uniform (order \<G>));
  b' :: bool \<leftarrow> \<A>2 c \<sigma>;
  return_spmf (b' = b)} ELSE coin_spmf"
    by(simp add: sample_uniform_one_time_pad)
  also have "... = TRY do {
  w :: nat \<leftarrow> sample_uniform (order \<G>);
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g (^) w, w);
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  c \<leftarrow> map_spmf (\<lambda> c'. \<^bold>g (^) c') (sample_uniform (order \<G>));
  b' :: bool \<leftarrow> \<A>2 c \<sigma>;
  map_spmf (op = b') coin_spmf} ELSE coin_spmf"
    by(simp add: sample_uniform_one_time_pad map_spmf_conv_bind_spmf[where p=coin_spmf])
  also have "... = TRY do {
  w :: nat \<leftarrow> sample_uniform (order \<G>);
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (\<^bold>g (^) w, w);
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  c' \<leftarrow> (sample_uniform (order \<G>));
  let c =  \<^bold>g (^) c';
  b' :: bool \<leftarrow> \<A>2 c \<sigma>;
  map_spmf (op = b') coin_spmf} ELSE coin_spmf"
    by(simp add: Let_def)
  also have "... = coin_spmf" 
    by(auto simp add:  try_bind_spmf_lossless2' map_eq_const_coin_spmf Let_def   )
  ultimately show ?thesis by simp
qed

theorem abstract_perfect_hiding: 
  shows "abstract_commitment.perfect_hiding \<A>"
  by(simp add: spmf_of_set perfect_hiding abstract_commitment.perfect_hiding_def)

lemma mod_one_cancel: assumes "[int y * z * x = y' * x] (mod order \<G>)" and "[z * x = 1] (mod order \<G>)"
  shows "[int y = y' * x] (mod order \<G>)"
  by (metis ab_semigroup_mult_class.mult_ac(1) cong_refl_int cong_scalar2_int cong_sym_int cong_trans_int mult.left_neutral semiring_normalization_rules(7) assms)

lemma dis_log_break:
  fixes z z' e e' :: nat
  assumes c: "c \<otimes> (\<^bold>g (^) w) (^) e = \<^bold>g (^) z"
    and c': "c \<otimes> (\<^bold>g (^) w) (^) e' = \<^bold>g (^) z'"
    and c_carrier: "c \<in> carrier \<G>"
    and w_less_order: "w < order \<G>"
    and gcd: "gcd (e - e') (order \<G>) = 1"
    and m_ge_m': "e > e'"
    and mm': "\<not> [e = e'] (mod order \<G>)"
  shows "w = nat ((int z - int z') * (fst (bezw (e -  e') (order \<G>))) mod order \<G>)" 
proof -
  have carrier1: "\<^bold>g (^) (w*e) \<in> carrier \<G>" by simp
  have carrier2: "inv (\<^bold>g (^) (w*e)) \<in> carrier \<G>" by simp
  have carrier3: "\<^bold>g (^) (w*e') \<in> carrier \<G>" by simp
  have carrier4: "inv (\<^bold>g (^) (w*e')) \<in> carrier \<G>" by simp
  have group_monoid: "Group.monoid \<G>" by simp
  have "c \<otimes> \<^bold>g (^) (w*e) = \<^bold>g (^) z" using c by(simp add: nat_pow_pow)
  then have "c \<otimes> \<^bold>g (^) (w*e) \<otimes> inv (\<^bold>g (^) (w*e)) = \<^bold>g (^) z \<otimes> inv (\<^bold>g (^) (w*e))" by simp
  then have "c \<otimes> (\<^bold>g (^) (w*e) \<otimes> inv (\<^bold>g (^) (w*e))) = \<^bold>g (^) z \<otimes> inv (\<^bold>g (^) (w*e))" 
  proof-
    have "c \<otimes> \<^bold>g (^) (w*e) \<otimes> inv (\<^bold>g (^) (w*e)) = c \<otimes> (\<^bold>g (^) (w*e) \<otimes> inv (\<^bold>g (^) (w*e)))"
    using carrier2 monoid.m_assoc[of "\<G>" "c" "\<^bold>g (^) (w*e)" "inv (\<^bold>g (^) (w*e))"] carrier1 group_monoid c_carrier
    by linarith
  then show ?thesis 
    by (simp add: \<open>c \<otimes> \<^bold>g (^) (w * e) = \<^bold>g (^) z\<close>)
  qed
  then have c1: "c = \<^bold>g (^) z \<otimes> inv (\<^bold>g (^) (w*e))" using carrier1 carrier2 
    by (simp add: c_carrier)
  have "c \<otimes> \<^bold>g (^) (w*e') = \<^bold>g (^) z'" using c' by(simp add: nat_pow_pow)
  then have "c \<otimes> \<^bold>g (^) (w*e') \<otimes> inv (\<^bold>g (^) (w*e')) = \<^bold>g (^) z' \<otimes> inv (\<^bold>g (^) (w*e'))" by simp
  then have "c \<otimes> (\<^bold>g (^) (w*e') \<otimes> inv (\<^bold>g (^) (w*e'))) = \<^bold>g (^) z' \<otimes> inv (\<^bold>g (^) (w*e'))" 
  proof-
    have "c \<otimes> \<^bold>g (^) (w*e') \<otimes> inv (\<^bold>g (^) (w*e')) = c \<otimes> (\<^bold>g (^) (w*e') \<otimes> inv (\<^bold>g (^) (w*e')))"
    using carrier4 monoid.m_assoc[of "\<G>" "c" "\<^bold>g (^) (w*e')" "inv (\<^bold>g (^) (w*e'))"] carrier3 group_monoid c_carrier
    by linarith
  then show ?thesis 
    by (simp add: \<open>c \<otimes> \<^bold>g (^) (w * e') = \<^bold>g (^) z'\<close>)
  qed
  then have c2: "c = \<^bold>g (^) z' \<otimes> inv (\<^bold>g (^) (w*e'))" using carrier1 carrier2 
    by (simp add: c_carrier)
  have "\<^bold>g (^) z \<otimes> inv (\<^bold>g (^) (w*e)) = \<^bold>g (^) z' \<otimes> inv (\<^bold>g (^) (w*e'))" using c1 c2 by simp
  then have "\<^bold>g (^) (z + order \<G> * e) \<otimes> inv (\<^bold>g (^) (w*e)) = \<^bold>g (^) (z' + order \<G> + order \<G> * e') \<otimes> inv (\<^bold>g (^) (w*e'))"   using  mod_mult_self2 pow_generator_mod
    by (metis mod_add_self2)  
  then have "\<^bold>g (^) (int z + int (order \<G>) * int e) \<otimes> inv (\<^bold>g (^) (int w* int e)) = \<^bold>g (^) (int z' + int (order \<G>) + int (order \<G>) * int e') \<otimes> inv (\<^bold>g (^) (int w* int e'))"
    by (metis (no_types, hide_lams) int_pow_int of_nat_add of_nat_mult) 
  then have int_exp: "\<^bold>g (^) (int z + int (order \<G>) * int e - int w* int e) = \<^bold>g (^) (int z' + int (order \<G>) + int (order \<G>) * int e' - int w* int e')"
    using int_pow_diff by simp
  have exp_lhs: "(int z + int (order \<G>) * int e - int w* int e) = (z + (order \<G>) * e - w* e)" 
  proof-
    have "z + (order \<G>) * e - w* e > 0" using w_less_order
      by (metis m_ge_m' mult.commute nat_mult_less_cancel_disj neq0_conv not_less0 trans_less_add2 zero_less_diff)
    then show ?thesis
      by (simp add: of_nat_diff) 
  qed
  have exp_rhs: "(int z' + int (order \<G>) + int (order \<G>) * int e' - int w* int e') = (z' + order \<G> + (order \<G>) * e' - w* e')"
  proof-
    have "(z' + order \<G> + (order \<G>) * e' - w* e') > 0" using w_less_order
      by (metis Nat.add_diff_assoc add_gr_0 less_imp_le_nat mult.commute nat_mult_le_cancel_disj order_gt_0) 
    then show ?thesis by (simp add: of_nat_diff) 
  qed
  have "\<^bold>g (^) (z + (order \<G>) * e - w* e) = \<^bold>g (^) (z' + order \<G> + (order \<G>) * e' - w* e')" using exp_lhs exp_rhs int_exp
    by (simp add: int_pow_int)
  then have "[(z + (order \<G>) * e - w* e) = (z' + order \<G> + (order \<G>) * e' - w* e')] (mod order \<G>)"
    by(simp add: pow_generator_eq_iff_cong finite_group)
  then have "[(z + (order \<G>) * e ) = (z' + order \<G> + (order \<G>) * e' - w* e' +  w* e)] (mod order \<G>)"
    by (metis (no_types, hide_lams) add.commute add_diff_inverse_nat cong_add_lcancel_nat distrib_right nat_diff_split nat_neq_iff trans_less_add1 w_less_order zero_less_diff)
  then have "[(z + (order \<G>) * e ) = (z' + order \<G> + (order \<G>) * e' + w* e -  w* e')] (mod order \<G>)"
   by (simp add: less_imp_le_nat trans_le_add2 w_less_order)
  then have "[(z + (order \<G>) * e ) = (z' + order \<G> + (order \<G>) * e' + w*(e -e'))] (mod order \<G>)"
    by (simp add: diff_mult_distrib2 less_imp_le_nat m_ge_m')
  then have "[z = z' + w*(e - e')] (mod order \<G>)"
    by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1) cong_nat_def mod_add_cong mod_add_self2 semiring_div_class.mod_mult_self4)
  then have "[int z = int z' + int w* int (e - e')] (mod order \<G>)"
    using transfer_int_nat_cong by force
  then have "[int z - int z' = int w* int (e - e')] (mod order \<G>)"
    by (metis add.commute cong_add_lcancel_int diff_add_cancel)
  then have "[int z - int z' = int w* (int e - int e')] (mod order \<G>)"
    by (simp add: less_imp_le_nat m_ge_m' of_nat_diff)
  then have "[(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) = int w* (int e - int e') * (fst (bezw (nat (int e - int e')) (order \<G>)))] (mod order \<G>)"
    using cong_scalar_int by blast
  then have "[(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) = int w* ((int e - int e') * (fst (bezw (nat (int e - int e')) (order \<G>))))] (mod order \<G>)"
    by (simp add: mult.assoc)
  then have "[(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) = int w* 1] (mod order \<G>)"
    using assms inverse
  proof -
    have f1: "int e - int e' = int e + - 1 * int e'"
      by auto
    have f2: "int w * 1 = int w"
      by simp
    have "nat (int e + - 1 * int e') = e - e'"
      by force
    then show ?thesis
      using f2 f1 by (metis \<open>[(int z - int z') * fst (bezw (nat (int e - int e')) (order \<G>)) = int w * (int e - int e') * fst (bezw (nat (int e - int e')) (order \<G>))] (mod int (order \<G>))\<close> cong_sym_int gcd inverse m_ge_m' schnorr_commitment.mod_one_cancel schnorr_commitment_axioms)  
  qed 
  then have "[(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) = int w] (mod order \<G>)"
    by simp
  then have "(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) mod order \<G> = int w mod order \<G>"
    using cong_int_def by blast
  then have "(int z - int z') * (fst (bezw (nat (int e - int e')) (order \<G>))) mod order \<G> = w mod int (order \<G>)"
    by (simp add: zmod_int)
  then have "w mod order \<G> = (int z - int z') * (fst (bezw (( e -  e')) (order \<G>))) mod order \<G> "
    by (metis int_minus nat_int zmod_int)
  then show ?thesis using w_less_order by simp
qed

lemma bind_game_eq_dis_log:
  shows "abstract_commitment.bind_game \<A> = discrete_log.dis_log (dis_log_\<A> \<A>)"
proof-
  have "abstract_commitment.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> gen;
    (c, e, z, e', z') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
    b \<leftarrow> verify vk e c z;
    b' \<leftarrow> verify vk e' c z';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: abstract_commitment.bind_game_def \<A>_cond_def) 
  also have "... = TRY do {
    w :: nat \<leftarrow> sample_uniform (order \<G>);
    (c, e, z, e', z') \<leftarrow> \<A> (\<^bold>g (^) w);
    _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
    b \<leftarrow> check (\<^bold>g (^) w) c e z;
    b' \<leftarrow> check (\<^bold>g (^) w) c e' z';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: gen_def split_def verify_def)
  also have "... = TRY do {
    w :: nat \<leftarrow> sample_uniform (order \<G>);
    (c, e, z, e', z') \<leftarrow> \<A> (\<^bold>g (^) w);
    _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
    _ :: unit \<leftarrow> assert_spmf (((c \<otimes> (\<^bold>g (^) w) (^) e) = \<^bold>g (^) z) \<and> (c \<otimes> (\<^bold>g (^) w) (^) e') = \<^bold>g (^) z');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: check_def)
  also have "... = TRY do {
    w :: nat \<leftarrow> sample_uniform (order \<G>);
    (c, e, z, e', z') \<leftarrow> \<A> (\<^bold>g (^) w);
    _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
    _ :: unit \<leftarrow> assert_spmf (((c \<otimes> (\<^bold>g (^) w) (^) e) = \<^bold>g (^) z) \<and> (c \<otimes> (\<^bold>g (^) w) (^) e') = \<^bold>g (^) z');
    return_spmf (w = nat ((int z - int z') * (fst (bezw (e -  e') (order \<G>))) mod order \<G>))} ELSE return_spmf False" 
    apply(intro try_spmf_cong)
    apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
    apply(rule dis_log_break) 
    by auto
  ultimately show ?thesis 
    by(simp add: discrete_log.dis_log_def dis_log_\<A>_def Let_def split_def cong: bind_spmf_cong_simp)
qed

end

locale asy_schnorr_commit =
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
  assumes schnorr_commitment: "\<And>n. schnorr_commitment (\<G> n)"
begin

sublocale schnorr_commitment "(\<G> n)" for n by(simp add: schnorr_commitment)

theorem correct: 
  shows "abstract_commitment.correct n m" 
  using abstract_correct by simp

theorem perfect_hiding:
  shows "abstract_commitment.perfect_hiding n (\<A> n)"
    by (simp add:  abstract_perfect_hiding)

theorem binding:
  shows "abstract_commitment.bind_advantage n (\<A> n) 
            = discrete_log.advantage n (dis_log_\<A> n (\<A> n))"
  by (simp add: discrete_log.advantage_def local.abstract_commitment.bind_advantage_def bind_game_eq_dis_log ) 

theorem "negligible (\<lambda> n. abstract_commitment.bind_advantage n (\<A> n)) 
            \<longleftrightarrow> negligible (\<lambda> n. discrete_log.advantage n (dis_log_\<A> n (\<A> n)))" 
  by(simp add: binding)

end

end