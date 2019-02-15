theory Abstract_Commitment imports
  CryptHOL.CryptHOL
begin

type_synonym ('vk', 'plain', 'commit', 'state) hid_adversary = 
  "('vk' \<Rightarrow> (('plain' \<times> 'plain') \<times> 'state) spmf)
   \<times> ('commit' \<Rightarrow> 'state \<Rightarrow> bool spmf)"

type_synonym ('ck', 'plain', 'commit', 'opening')  bind_adv = 
  "'ck' \<Rightarrow> ('commit' \<times> 'plain' \<times> 'opening' \<times> 'plain' \<times> 'opening') spmf"

locale abstract_commitment =
  fixes key_gen :: "('ck \<times> 'vk) spmf"
  and commit :: "'ck \<Rightarrow> 'plain \<Rightarrow> ('commit \<times> 'opening) spmf"
  and verify :: "'vk \<Rightarrow> 'plain \<Rightarrow> 'commit \<Rightarrow> 'opening \<Rightarrow> bool spmf"
  and valid_msg :: "'plain \<Rightarrow> bool"
  and \<A>_cond :: "'commit \<Rightarrow> 'plain \<Rightarrow> 'opening \<Rightarrow> 'plain \<Rightarrow> 'opening \<Rightarrow> bool"
begin

definition lossless :: "('pub_key, 'plain, 'commit, 'state) hid_adversary \<Rightarrow> bool"
where "lossless \<A> \<longleftrightarrow>
   ((\<forall>pk. lossless_spmf (fst \<A> pk)) \<and>
        (\<forall>commit \<sigma>. lossless_spmf (snd \<A> commit \<sigma>)))"

definition correct_game :: "'plain \<Rightarrow> bool spmf"
where "correct_game m = do {
  (ck, vk) \<leftarrow> key_gen;
  (c,d) \<leftarrow> commit ck m;
  verify vk m c d }"

lemma   "\<lbrakk> lossless_spmf key_gen; lossless_spmf TI;
          \<And>pk m. valid_msg m \<Longrightarrow> lossless_spmf (commit pk m);
            \<And>pk m c d. valid_msg m \<Longrightarrow> lossless_spmf (verify pk m c d) \<rbrakk>
              \<Longrightarrow> valid_msg m \<Longrightarrow> lossless_spmf (correct_game m)"
by(simp add: lossless_def correct_game_def split_def Let_def)

definition correct :: "'plain \<Rightarrow> bool"
where "correct m  \<equiv> spmf (correct_game m) True = 1"

primrec hiding_game :: "('vk, 'plain, 'commit, 'state) hid_adversary \<Rightarrow> bool spmf"
where "hiding_game (\<A>1, \<A>2) = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
  _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
  b \<leftarrow> coin_spmf; 
  (c,d) \<leftarrow> commit ck (if b then m0 else m1);
  b' \<leftarrow> \<A>2 c \<sigma>;
  return_spmf (b' = b)} ELSE coin_spmf"

lemma lossless_hiding_game:
  "\<lbrakk> lossless \<A>; lossless_spmf key_gen;
     \<And>pk plain. valid_msg plain \<Longrightarrow> lossless_spmf (commit pk plain) \<rbrakk>
  \<Longrightarrow> lossless_spmf (hiding_game \<A>)"
  by(auto simp add: lossless_def hiding_game_def split_def Let_def)

definition hiding_advantage :: "('vk, 'plain, 'commit, 'state) hid_adversary \<Rightarrow> real"
  where "hiding_advantage \<A> \<equiv> spmf (hiding_game \<A>) True"

definition perfect_hiding :: "('vk, 'plain, 'commit, 'state) hid_adversary \<Rightarrow> bool"
where "perfect_hiding \<A> \<equiv> (spmf (hiding_game \<A>) True = 1/2)"

definition bind_game :: "('ck, 'plain, 'commit, 'opening) bind_adv \<Rightarrow> bool spmf"
where "bind_game \<A>  = TRY do {
  (ck, vk) \<leftarrow> key_gen;
  (c, m, d, m', d') \<leftarrow> \<A> ck;
  _ :: unit \<leftarrow> assert_spmf (\<A>_cond c m d m' d');
  b \<leftarrow> verify vk m c d;
  b' \<leftarrow> verify vk m' c d';
  _ :: unit \<leftarrow> assert_spmf (b \<and> b'); 
  return_spmf True} ELSE return_spmf False"

lemma lossless_binding_game: "lossless_spmf (bind_game \<A>)" 
  by (simp add: bind_game_def)

definition bind_advantage :: "('ck, 'plain, 'commit, 'opening) bind_adv \<Rightarrow> real"
  where "bind_advantage \<A> \<equiv> spmf (bind_game \<A>) True"

end

end