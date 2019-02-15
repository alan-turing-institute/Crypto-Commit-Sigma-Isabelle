theory DL_Equality_Sigma_Commit imports  
  Abstract_Commitment
  Abstract_Sigma_Protocols
  Cyclic_Group_Ext
  Discrete_log
  GCD
  Uniform_Sampling 
  Uniform_Sampling_Defs
begin 

locale schnorr_2_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
    and x :: nat
    and g' :: 'grp
  assumes finite_group: "finite (carrier \<G>)"
    and order_gt_2: "order \<G> > 2"
    and prime_order: "prime (order \<G>)"
    and prime_field: "a < (order \<G>) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a (order \<G>)"
    and g': "g' = \<^bold>g (^) x"
begin

lemma or_gt_0 [simp]:"order \<G> > 0" 
  using order_gt_2 by simp

lemma lossless_samp_uni_excl: "lossless_spmf (samp_uni_excl (order \<G>) p)"
proof-
  have "order \<G> > 1" using order_gt_2 by simp
  then show ?thesis 
    by (metis Diff_empty samp_uni_excl_def Diff_eq_empty_iff One_nat_def card_empty card_insert_disjoint card_lessThan equals0D finite_Diff_insert finite_lessThan lessThan_iff less_not_refl3 lossless_spmf_of_set subset_singletonD)
qed

lemma lossless_samp_uni: "lossless_spmf (sample_uniform (order \<G>))"
  using order_gt_2 by simp

lemma lossless_samp_uni_units: "lossless_spmf (samp_uni_units (order \<G>))"
  apply(simp add: samp_uni_units_def) using order_gt_2 by fastforce

lemma weight_samp_uni_units: "weight_spmf (samp_uni_units (order \<G>)) = 1"
  using lossless_samp_uni_units
  by (simp add: lossless_spmf_def)

lemma [simp]: "set_spmf (samp_uni_units (order \<G>)) = {..< order \<G>} - {0}"
  by(simp add: samp_uni_units_def)

lemma [simp]: "set_spmf (samp_uni_units_excl (order \<G>) p) = ({..< order \<G>} - {p} - {0})"
  by(simp add: samp_uni_units_excl_def)

lemma lossless_samp_uni_units_excl: "lossless_spmf (samp_uni_units_excl (order \<G>) p)"
  apply(simp add: samp_uni_units_excl_def) using order_gt_2 
  by (smt Diff_empty Diff_insert0 One_nat_def Suc_leI card.insert card_empty card_lessThan finite.intros(1) finite_insert insert_Diff insert_absorb leD nat_neq_iff prime_gt_1_nat prime_order subset_singletonD two_is_prime_nat zero_le_one)
 
definition "challenge = samp_uni_units (order \<G>)"

definition "snd_challenge p = samp_uni_units_excl (order \<G>) p"

definition "response r w e = return_spmf ((w*e + r) mod (order \<G>))"

type_synonym witness = "nat"
type_synonym rand = nat 
type_synonym 'grp' msg = "'grp' \<times> 'grp'"
type_synonym response = nat
type_synonym challenge = nat
type_synonym 'grp' pub_in = "'grp' \<times> 'grp'"

definition init :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> (rand \<times> 'grp msg) spmf"
  where "init h w = do {
    let (h, h') = h;  
    r \<leftarrow> sample_uniform (order \<G>);
    return_spmf (r, \<^bold>g (^) r, g' (^) r)}"

definition check :: "'grp pub_in \<Rightarrow> 'grp msg \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool spmf"
  where "check h a e z = 
    return_spmf (fst a \<otimes> (fst h (^) e) = \<^bold>g (^) z \<and> snd a \<otimes> (snd h (^) e) = g' (^) z)"

definition R :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> bool"
  where "R h w \<equiv> (fst h = \<^bold>g (^) w \<and> w \<noteq> 0 \<and> w < order \<G> \<and> snd h = g' (^) w)"

definition R2 :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> ('grp msg, challenge, response) conv_tuple spmf"
  where "R2 H w = do {
  let (h, h') = H;
  (r, a, a') \<leftarrow> init H w; 
  c \<leftarrow> samp_uni_units (order \<G>);
  let z = (w*c + r) mod (order \<G>);
  return_spmf ((a,a'),c, z)}"

definition S2 :: "'grp pub_in \<Rightarrow> challenge \<Rightarrow> ('grp msg, challenge, response) conv_tuple spmf"
  where "S2 H c = do {
  let (h, h') = H;
  z \<leftarrow> (sample_uniform (order \<G>));
  let a = \<^bold>g (^) z \<otimes> inv (h (^) c); 
  let a' =  g' (^) z \<otimes> inv (h' (^) c);
  return_spmf ((a,a'),c, z)}"

definition pk_adversary2 :: "'grp pub_in \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> nat spmf"
  where "pk_adversary2 x' c1 c2 = do {
    let ((a,a'), e, z) = c1;
    let ((b,b'), e', z') = c2;
    return_spmf (if e > e' then (nat ((int z - int z') * (fst (bezw (e - e') (order \<G>))) mod order \<G>)) else 
(nat ((int z' - int z) * (fst (bezw (e' - e) (order \<G>))) mod order \<G>)))}"

sublocale epsilon_protocols_base: epsilon_protocols_base init challenge snd_challenge response check R S2 .

lemma R2_eq_R: "R2 h w = epsilon_protocols_base.R h w"
  unfolding  R2_def epsilon_protocols_base.R_def Let_def 
  by(simp add: challenge_def response_def split_def)

end 

locale schnorr_2 = schnorr_2_base + cyclic_group \<G>
begin

lemma zr: 
  assumes z: "z = (w*c + r) mod (order \<G>)" 
    and x: "w < order \<G>" 
    and c: "c < order \<G>" 
    and r: "r < order \<G>"
  shows "(z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>) = r"
proof-
  have cong: "[z + (order \<G>)*(order \<G>) = w*c + r] (mod (order \<G>))" 
    by(simp add: cong_nat_def z)
  hence "[z + (order \<G>)*(order \<G>) - w*c = r] (mod (order \<G>))" 
  proof-
    have "z + (order \<G>)*(order \<G>) > w*c" 
      using x c by (simp add: mult_strict_mono trans_less_add2)
    then show ?thesis
      by (metis cong add_diff_inverse_nat cong_add_lcancel_nat less_imp_le linorder_not_le) 
  qed
  then show ?thesis
    by(simp add: cong_nat_def r)
qed

lemma xr':assumes x: "w < order \<G>" 
    and c: "c < order \<G>" 
    and r: "r < order \<G>"
  shows "((w*c + r) mod (order \<G>) mod (order \<G>) + (order \<G>)*(order \<G>) - w*c) mod (order \<G>) = r"
  using assms zr by simp

lemma complete: assumes "h = (\<^bold>g (^) (w::nat), g' (^) w)"
  shows "spmf (epsilon_protocols_base.completeness_game h w) True = 1"
proof-
  have "\<^bold>g (^) y \<otimes> (\<^bold>g (^) w) (^) e = \<^bold>g (^) ((w * e + y))" for y e
    by (simp add: add.commute nat_pow_pow nat_pow_mult) 
  also have "(\<^bold>g (^) x) (^) y \<otimes> ((\<^bold>g (^) x) (^) w) (^) e = (\<^bold>g (^) x) (^) ((w * e + y) mod (order \<G>))" for y e
    by (metis add.commute nat_pow_pow nat_pow_mult  pow_generator_mod generator_closed nat_pow_closed mod_mult_right_eq)  
  ultimately show ?thesis
    unfolding  epsilon_protocols_base.completeness_game_def init_def check_def
    by(simp add: Let_def bind_spmf_const  pow_generator_mod order_gt_2 weight_samp_uni_units lossless_weight_spmfD init_def challenge_def response_def g' assms)
qed

lemma completeness: 
  shows "epsilon_protocols_base.completeness h w"
  apply(simp add: epsilon_protocols_base.completeness_def R_def) 
  by (metis prod.collapse complete) 

lemma h_sub:
  assumes "h = \<^bold>g (^) w" and x_not_0: "w \<noteq> 0" and w: "w < order \<G>" and z: "z < order \<G>" and c: "c < order \<G>"
  shows "\<^bold>g (^) ((z + (order \<G>)*(order \<G>) - w*c)) = \<^bold>g (^) z \<otimes> inv (h (^) c)" 
(is "?lhs = ?rhs")
proof-
  have "(z + order \<G> * order \<G> - w * c) = (z + (order \<G> * order \<G> - w * c))"
    using w c z by (simp add: less_imp_le_nat mult_le_mono) 
  then have lhs: "?lhs = \<^bold>g (^) z \<otimes> \<^bold>g (^) ((order \<G>)*(order \<G>) - w*c)" by(simp add: nat_pow_mult)
  have " \<^bold>g (^) ((order \<G>)*(order \<G>) - w*c) =  inv (h (^) c)"  
  proof-
    have "((order \<G>)*(order \<G>) - w*c) > 0" using assms
      by (simp add: mult_strict_mono)
    then have " \<^bold>g (^) ((order \<G>)*(order \<G>) - w*c) =  \<^bold>g (^) int ((order \<G>)*(order \<G>) - w*c)"
      by (simp add: int_pow_int) 
    also have "... = \<^bold>g (^) int ((order \<G>)*(order \<G>)) \<otimes> inv (\<^bold>g (^) (w*c))" 
      using int_pow_diff[of "\<^bold>g" "order \<G> * order \<G>" "w * c"]
      by (smt \<open>0 < order \<G> * order \<G> - w * c\<close> generator_closed group.int_pow_def2 group_l_invI int_minus int_pow_int l_inv_ex of_nat_less_iff zero_less_diff) 
    also have "... = \<^bold>g (^) ((order \<G>)*(order \<G>)) \<otimes> inv (\<^bold>g (^) (w*c))"
      by (metis int_pow_int) 
    also have "... = \<^bold>g (^) ((order \<G>)*(order \<G>)) \<otimes> inv ((\<^bold>g (^) w) (^) c)"
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

lemma h_sub2:
  assumes  "h' = g' (^) w" and x_not_0: "w \<noteq> 0" and w: "w < order \<G>" and z: "z < order \<G>" and c: "c < order \<G>"
  shows "g' (^) ((z + (order \<G>)*(order \<G>) - w*c))  = g' (^) z \<otimes> inv (h' (^) c)" 
(is "?lhs = ?rhs")
proof-
  have "g' = \<^bold>g (^) x" using g' by simp
  have g'_carrier: "g' \<in> carrier \<G>" using g' by simp
  have 1: "g' (^) ((order \<G>)*(order \<G>) - w*c) = inv (h' (^) c)"
  proof-
    have "((order \<G>)*(order \<G>) - w*c) > 0" using assms
      by (simp add: mult_strict_mono)
    then have " g' (^) ((order \<G>)*(order \<G>) - w*c) =  g' (^) int ((order \<G>)*(order \<G>) - w*c)"
      by (simp add: int_pow_int) 
    also have "... = g' (^) int ((order \<G>)*(order \<G>)) \<otimes> inv (g' (^) (w*c))" 
      using int_pow_diff[of "g'" "order \<G> * order \<G>" "w * c"] g'_carrier
    proof -
      have "\<forall>x0 x1. int x1 - int x0 = int x1 + - 1 * int x0"
        by auto
      then have f1: "g' (^) int (order \<G> * order \<G> - w * c) = g' (^) nat (int (order \<G> * order \<G>) + - 1 * int (w * c))"
        by (metis (no_types) int_minus int_pow_int)
      have f2: "0 \<le> int (order \<G> * order \<G>) + - 1 * int (w * c)"
        using \<open>(0::nat) < order \<G> * order \<G> - (w::nat) * (c::nat)\<close> by linarith
      have f3: "\<forall>p a i. \<not> Group.group (p::\<lparr>carrier :: 'a set, monoid.mult :: _ \<Rightarrow> _ \<Rightarrow> _, one :: _, generator :: 'a\<rparr>) \<or> a (^)\<^bsub>p\<^esub> i = (if 0 \<le> i then a (^)\<^bsub>p\<^esub> nat i else inv\<^bsub>p\<^esub> (a (^)\<^bsub>p\<^esub> nat (- 1 * i)))"
        by (simp add: group.int_pow_def2)
      have f4: "\<forall>x0 x1. (x1::int) - x0 = - 1 * x0 + x1"
        by auto
      have "- 1 * int (w * c) + int (order \<G> * order \<G>) = int (order \<G> * order \<G>) + - 1 * int (w * c)"
        by presburger
      then show ?thesis
        using f4 f3 f2 f1 by (metis (full_types) g'_carrier group.int_pow_diff group_l_invI int_pow_int l_inv_ex)
    qed 
    also have "... = g' (^) ((order \<G>)*(order \<G>)) \<otimes> inv (g' (^) (w*c))" 
      by (metis int_pow_int) 
    also have "... = g' (^) ((order \<G>)*(order \<G>)) \<otimes> inv (h' (^) c)"
      by(simp add: nat_pow_pow g'_carrier assms)
    also have "... = \<one> \<otimes> inv (h' (^) c)"
      using generator_pow_mult_order
      by (metis g' generator_closed mult.commute nat_pow_one nat_pow_pow) 
    ultimately show ?thesis
      by (simp add: assms(1) g'_carrier) 
  qed
  have "(z + order \<G> * order \<G> - w * c) = (z + (order \<G> * order \<G> - w * c))"
    using w c z by (simp add: less_imp_le_nat mult_le_mono) 
  then have lhs: "?lhs = g' (^) z \<otimes> g' (^) ((order \<G>)*(order \<G>) - w*c)" 
    by(auto simp add: nat_pow_mult g'_carrier)
  then show ?thesis using 1 by simp
qed

lemma hv_zk2: assumes "H = (\<^bold>g (^) (w::nat), g' (^) w)" and "w \<noteq> 0" and "w < order \<G>"
  shows "epsilon_protocols_base.R H w = bind_spmf challenge (S2 H)"
  including monad_normalisation
proof-
  have  "R2 H w = bind_spmf challenge (S2 H)"
  proof-
    have g'_carrier: "g' \<in> carrier \<G>" using g' by simp
    have "R2 H w = do {
    let (h, h') = H;
      r \<leftarrow> sample_uniform (order \<G>);
    let (r, a, a') =  (r, \<^bold>g (^) r, g' (^) r);
    c \<leftarrow> samp_uni_units (order \<G>);
    let z = (w*c + r) mod (order \<G>);
    return_spmf ((a,a'),c, z)}"
      by(simp add: R2_def init_def)
    also have "... = do {
    let (h, h') = H;
    r \<leftarrow> sample_uniform (order \<G>);
    c \<leftarrow> samp_uni_units (order \<G>);
    let z = (w*c + r) mod (order \<G>);
    let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>)); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
      apply(simp add: Let_def R2_def init_def)
      using assms xr' by(simp cong: bind_spmf_cong_simp)
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> map_spmf (\<lambda> r. (w*c + r) mod (order \<G>)) (sample_uniform (order \<G>));
    let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>)); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
      by(simp add: bind_map_spmf Let_def o_def)
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>)); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
      by(simp add: samp_uni_plus_one_time_pad)
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> (sample_uniform (order \<G>));
    let a = \<^bold>g (^) ((z + (order \<G>)*(order \<G>) - w*c)); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
      by(simp add: g' pow_generator_mod)
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> (sample_uniform (order \<G>));
      let a = \<^bold>g (^) z \<otimes> inv (h (^) c); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c) mod (order \<G>));
    return_spmf ((a,a'),c, z)}"
      using h_sub assms by(simp cong: bind_spmf_cong_simp)
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> (sample_uniform (order \<G>));
      let a = \<^bold>g (^) z \<otimes> inv (h (^) c); 
    let a' = g' (^) ((z + (order \<G>)*(order \<G>) - w*c));
    return_spmf ((a,a'),c, z)}"
      using g'_carrier pow_carrier_mod[of "g'"] by simp
    also have "... = do {
    let (h, h') = H;
    c \<leftarrow> samp_uni_units (order \<G>);
    z \<leftarrow> (sample_uniform (order \<G>));
      let a = \<^bold>g (^) z \<otimes> inv (h (^) c); 
    let a' =  g' (^) z \<otimes> inv (h' (^) c);
    return_spmf ((a,a'),c, z)}"
      using h_sub2 assms by(simp cong: bind_spmf_cong_simp)
    ultimately show ?thesis 
      unfolding challenge_def S2_def init_def   
      by(simp add: split_def Let_def)
  qed
  thus ?thesis using R2_eq_R by simp
qed

lemma inverse: assumes "gcd w (order \<G>) = 1" 
  shows "[w * (fst (bezw w (order \<G>))) = 1] (mod order \<G>)"
proof-
  have 2: "fst (bezw  w (order \<G>)) * w + snd (bezw w (order \<G>)) * int (order \<G>) = 1" 
    using bezw_aux assms int_minus by presburger 
  hence 3: "(fst (bezw  w (order \<G>)) * w + snd (bezw w (order \<G>)) * int (order \<G>)) mod (order \<G>) = 1 mod (order \<G>)" 
    by (simp add: zmod_int)
  hence 4: "(fst (bezw w (order \<G>)) * w) mod (order \<G>) = 1 mod (order \<G>)"
    by simp 
  hence 5:  "[(fst (bezw w (order \<G>))) * w  = 1] (mod order \<G>)" 
    using 2 3 cong_int_def by auto
  then show ?thesis by(simp add: mult.commute) 
qed

lemma witness_find:
  assumes "ya < order \<G>" and "yb < order \<G>" and "y < order \<G>" and w: "w < order \<G>" and "h = \<^bold>g (^) w" and "ya \<noteq> yb" and "w \<noteq> 0"
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
    by (metis (no_types, hide_lams) gcd inverse[of "ya - yb"] cong_scalar_int cong_sym_int cong_trans_int mult.commute mult.left_neutral)  
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

lemma honest_verifier_ZK2: 
  shows "epsilon_protocols_base.honest_V_ZK H w"
    unfolding epsilon_protocols_base.honest_V_ZK_def R_def
    using  hv_zk2[of "H" "w"] 
    by (metis prod.collapse)

lemma special_soundness:
  shows "epsilon_protocols_base.special_soundness h w"
proof-
  {assume w1: "w \<noteq> 0" and w2: "w < order \<G>"
    have "local.epsilon_protocols_base.special_soundness_game h w pk_adversary2 = return_spmf True"
      (is "?lhs = ?rhs")
  proof-
    have "?lhs = do {
      y \<leftarrow> sample_uniform (order \<G>);
      ya \<leftarrow> samp_uni_units (order \<G>);
      yb \<leftarrow> samp_uni_units_excl (order \<G>) ya;
      return_spmf (w = (if (ya > yb) then nat ((int ((w * ya + y) mod order \<G>) - int ((w * yb + y) mod order \<G>)) * fst (bezw (ya - yb) (order \<G>)) mod int (order \<G>)) 
          else nat ((int ((w * yb + y) mod order \<G>) - int ((w * ya + y) mod order \<G>)) * fst (bezw (yb - ya) (order \<G>)) mod int (order \<G>))))}"
       unfolding local.epsilon_protocols_base.special_soundness_game_def pk_adversary2_def 
       by(simp add: response_def challenge_def init_def snd_challenge_def)
     then show ?thesis 
       by(simp add: lossless_samp_uni_units lossless_samp_uni_units_excl witness_find w1 w2 bind_spmf_const lossless_samp_uni_excl lossless_samp_uni  lossless_weight_spmfD cong: bind_spmf_cong_simp)
  qed }
  then have "w \<noteq> 0 \<Longrightarrow> w < order \<G> \<Longrightarrow> spmf (local.epsilon_protocols_base.special_soundness_game h w pk_adversary2) True = 1"
     by simp
  then show ?thesis unfolding epsilon_protocols_base.special_soundness_def R_def by auto
qed

theorem "epsilon_protocols_base.\<Sigma>_protocol h w"
  by(simp add: epsilon_protocols_base.\<Sigma>_protocol_def completeness honest_verifier_ZK2 special_soundness)

end

locale asy_schnorr_2 = 
 fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
 assumes schnorr_2: "\<And>n. schnorr_2 (\<G> n) x g'"
begin

sublocale schnorr_2 "(\<G> n)" for n by(simp add: schnorr_2)

theorem "epsilon_protocols_base.\<Sigma>_protocol n g' h w" 
  by (simp add: completeness honest_verifier_ZK2 local.epsilon_protocols_base.\<Sigma>_protocol_def special_soundness)

end

end