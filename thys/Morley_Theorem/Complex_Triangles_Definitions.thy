theory Complex_Triangles_Definitions

imports Complex_Angles

begin

section \<open>Complex triangles\<close>
text \<open>In this section we define triangles and derive some useful lemmas on congruent 
triangles, following the model \cite{Triangle-AFP}\<close>

locale congruent_ctriangle =
  fixes a1 b1 c1 :: "complex" and a2 b2 c2 :: "complex"
  assumes sides':  "cdist a1 b1 = cdist a2 b2" "cdist a1 c1 = cdist a2 c2" "cdist b1 c1 = cdist b2 c2"
    and angles': "angle_c b1 a1 c1 = angle_c b2 a2 c2 \<or> angle_c b1 a1 c1 = - angle_c b2 a2 c2" 
    "angle_c a1 b1 c1 = angle_c a2 b2 c2 \<or> angle_c a1 b1 c1 = - angle_c a2 b2 c2"
    "angle_c a1 c1 b1 = angle_c a2 c2 b2 \<or> angle_c a1 c1 b1 = - angle_c a2 c2 b2"
begin

lemma sides:
  "cdist a1 b1 = cdist a2 b2" "cdist a1 c1 = cdist a2 c2" "cdist b1 c1 = cdist b2 c2"
  "cdist b1 a1 = cdist a2 b2" "cdist c1 a1 = cdist a2 c2" "cdist c1 b1 = cdist b2 c2"
  "cdist a1 b1 = cdist b2 a2" "cdist a1 c1 = cdist c2 a2" "cdist b1 c1 = cdist c2 b2"
  "cdist b1 a1 = cdist b2 a2" "cdist c1 a1 = cdist c2 a2" "cdist c1 b1 = cdist c2 b2"
  using sides' 
  by (auto simp add: norm_minus_commute) 

lemma angles:
  "angle_c b1 a1 c1 = angle_c b2 a2 c2 \<or> angle_c b1 a1 c1 = - angle_c b2 a2 c2" 
  "angle_c a1 b1 c1 = angle_c a2 b2 c2 \<or> angle_c a1 b1 c1 = - angle_c a2 b2 c2" 
  "angle_c a1 c1 b1 = angle_c a2 c2 b2 \<or> angle_c a1 c1 b1 = - angle_c a2 c2 b2"
  "angle_c c1 a1 b1 = angle_c b2 a2 c2 \<or> angle_c c1 a1 b1 = - angle_c b2 a2 c2" 
  "angle_c c1 b1 a1 = angle_c a2 b2 c2 \<or> angle_c c1 b1 a1 = - angle_c a2 b2 c2" 
  "angle_c b1 c1 a1 = angle_c a2 c2 b2 \<or> angle_c b1 c1 a1 = - angle_c a2 c2 b2"
  "angle_c b1 a1 c1 = angle_c c2 a2 b2 \<or> angle_c b1 a1 c1 = - angle_c c2 a2 b2" 
  "angle_c a1 b1 c1 = angle_c c2 b2 a2 \<or> angle_c a1 b1 c1 = - angle_c c2 b2 a2" 
  "angle_c a1 c1 b1 = angle_c b2 c2 a2 \<or> angle_c a1 c1 b1 = - angle_c b2 c2 a2"
  "angle_c c1 a1 b1 = angle_c c2 a2 b2 \<or> angle_c c1 a1 b1 = - angle_c c2 a2 b2" 
  "angle_c c1 b1 a1 = angle_c c2 b2 a2 \<or> angle_c c1 b1 a1 = - angle_c c2 b2 a2" 
  "angle_c b1 c1 a1 = angle_c b2 c2 a2 \<or> angle_c b1 c1 a1 = - angle_c b2 c2 a2"
  using angles' angle_c_commute 
  by(simp_all add:  angle_c_commute)(metis add.inverse_inverse angle_c_commute)+

end



end