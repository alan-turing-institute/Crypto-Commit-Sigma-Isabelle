theory Abstract_Sigma_Protocols imports 
  SPMF
begin

type_synonym ('msg', 'challenge', 'response') conv_tuple = "('msg' \<times> 'challenge' \<times> 'response')"
type_synonym ('pub_input', 'msg', 'challenge', 'response', 'witness') prover_adversary 
                  = "'pub_input' \<Rightarrow> ('msg', 'challenge', 'response') conv_tuple 
                        \<Rightarrow> ('msg', 'challenge', 'response') conv_tuple \<Rightarrow> 'witness' spmf"

locale epsilon_protocols_base =
  fixes init :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> ('rand \<times> 'msg) spmf"
    and challenge :: "'challenge spmf"
    and snd_challenge :: "'challenge \<Rightarrow> 'challenge spmf"
    and response :: "'rand \<Rightarrow> 'witness \<Rightarrow> 'challenge  \<Rightarrow> 'response spmf"
    and check :: "'pub_input \<Rightarrow> 'msg \<Rightarrow> 'challenge \<Rightarrow> 'response \<Rightarrow> bool spmf"
    and Rel :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> bool"
    and S :: "'pub_input \<Rightarrow> 'challenge \<Rightarrow> ('msg, 'challenge, 'response) conv_tuple spmf"
begin

(*h is public input, w is witness*)

definition completeness_game :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> bool spmf"
  where "completeness_game h w = do {
    (r, a) \<leftarrow> init h w;
    e \<leftarrow> challenge;
    z \<leftarrow> response r w e;
    check h a e z}" 

definition "completeness h w \<equiv> (Rel h w \<longrightarrow> spmf (completeness_game h w) True = 1)"

definition special_soundness_game :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> ('pub_input, 'msg, 'challenge, 'response, 'witness) prover_adversary \<Rightarrow> bool spmf"
  where "special_soundness_game h w \<A> = do {
    (r, a) \<leftarrow> init h w;
    e \<leftarrow> challenge;
    z \<leftarrow> response r w e;
    e' \<leftarrow> snd_challenge e;
    z' \<leftarrow> response r w e'; 
    let conv_1 = (a, e, z);
    let conv_2 = (a, e', z');
    w' \<leftarrow> \<A> h conv_1 conv_2;
    return_spmf (w = w')}"  

definition R :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> ('msg, 'challenge, 'response) conv_tuple spmf"
  where "R h w = do { 
    (r,a) \<leftarrow> init h w;
    c \<leftarrow> challenge;
    z \<leftarrow> response r w c;
    return_spmf (a,c,z)}"

definition "special_soundness h w \<equiv> \<exists> \<A>. Rel h w \<longrightarrow> (spmf (special_soundness_game h w \<A>) True = 1)"

definition "honest_V_ZK h w \<equiv> (Rel h w \<longrightarrow> R h w = bind_spmf challenge (S h))"

definition "\<Sigma>_protocol h w \<equiv> completeness h w \<and> special_soundness h w \<and> honest_V_ZK h w"

end

end
    