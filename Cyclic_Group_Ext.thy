theory Cyclic_Group_Ext imports 
  CryptHOL.CryptHOL
  "HOL-Number_Theory.Cong"
  GCD
begin

context cyclic_group begin

lemma generator_pow_order: "\<^bold>g (^) order G = \<one>"
proof(cases "order G > 0")
  case True
  hence fin: "finite (carrier G)" by(simp add: order_gt_0_iff_finite)
  then have [symmetric]: "(\<lambda>x. x \<otimes> \<^bold>g) ` carrier G = carrier G"
    by(rule endo_inj_surj)(auto simp add: inj_on_multc)
  then have "carrier G = (\<lambda> n. \<^bold>g (^) Suc n) ` {..<order G}" using fin 
    by(simp add: carrier_conv_generator image_image)
  then obtain n where n: "\<one> = \<^bold>g (^) Suc n" "n < order G" by auto
  have "n = order G - 1" using n inj_onD[OF inj_on_generator, of 0 "Suc n"] by fastforce
  with True n show ?thesis by auto
qed simp

lemma generator_pow_mult_order: "\<^bold>g (^) (order G * order G) = \<one>"
  using generator_pow_order 
  by (metis generator_closed nat_pow_one nat_pow_pow)

lemma pow_generator_mod: "\<^bold>g (^) (k mod order G) = \<^bold>g (^) k"
proof(cases "order G > 0")
  case True
  obtain n where n: "k = n * order G + k mod order G" by (metis div_mult_mod_eq)
  have "\<^bold>g (^) k = (\<^bold>g (^) order G) (^) n \<otimes> \<^bold>g (^) (k mod order G)" 
    by(subst n)(simp add: nat_pow_mult nat_pow_pow mult_ac)
  then show ?thesis by(simp add: generator_pow_order)
qed simp

lemma pow_carrier_mod: assumes "g \<in> carrier G" 
  shows "g (^) (k mod order G) = g (^) k"
  using pow_generator_mod 
  by (metis assms generatorE generator_closed mod_mult_right_eq nat_pow_pow)

lemma pow_generator_eq_iff_cong:
  "finite (carrier G) \<Longrightarrow> \<^bold>g (^) x = \<^bold>g (^) y \<longleftrightarrow> [x = y] (mod order G)"
by(subst (1 2) pow_generator_mod[symmetric])(auto simp add: cong_nat_def order_gt_0_iff_finite intro: inj_onD[OF inj_on_generator])

lemma inverse: assumes "gcd (nat (int m - int m')) (order \<G>) = 1" and m_ge_m': "m > m'"
  shows "[(int m - int m') * (fst (bezw (nat (int m - int m')) (order \<G>))) = 1] (mod order \<G>)"
proof-
  have 4: "int m - int m' = int (m - m')" using m_ge_m' by simp
  have 1: "fst (bezw  (nat (int m - int m')) (order \<G>)) * int (m - m') + snd (bezw (nat (int m - int m')) (order \<G>)) * int (order \<G>) = 1" 
    using bezw_aux assms int_minus by presburger 
  hence 2: "(fst (bezw  (nat (int m - int m')) (order \<G>)) * int (m - m') + snd (bezw (nat (int m - int m')) (order \<G>)) * int (order \<G>)) mod (order \<G>) = 1 mod (order \<G>)" 
    by (simp add: zmod_int)
  hence 3: "(fst (bezw (nat (int m - int m')) (order \<G>)) * int  (m - m')) mod (order \<G>) = 1 mod (order \<G>)"
    by simp 
  hence 5:  "[(fst (bezw (nat (int m - int m')) (order \<G>))) *(int m - int m')  = 1] (mod order \<G>)" 
    using 1 2 4 cong_int_def by auto
  then show ?thesis by(simp add: mult.commute) 
qed

end

end