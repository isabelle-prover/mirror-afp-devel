theory KZG_def

imports Polynomial_Commitment_Schemes Primitives
begin

text \<open>In this theory we formalize the KZG polynomial commitment scheme as introduced in Kate,
Zaverucha, and Goldberg's ``Constant-Size Commitments to Polynomials and Their Applications''
\<^cite>\<open>KZG10\<close>.\<close>

section \<open>KZG function definitions\<close>

text \<open>Define the KZG with functions that match the abstract polynomial commitment scheme and 
instantiate the KZG as a polynomial commitment scheme.\<close>

locale KZG = math_primitives
begin

type_synonym trapdoor = unit
type_synonym 'a' ck = "'a' list"
type_synonym 'a' vk = "'a' list"
type_synonym 'a' commit = "'a'"
type_synonym 'e' argument = "'e' mod_ring"
type_synonym 'e' evaluation = "'e' mod_ring"
type_synonym 'a' witness = "'a'"

subsection \<open>Setup\<close>

text \<open>We do not compute the Groups for the bilinear pairing but assume them and compute 
a uniformly random secret key \<open>\<alpha>\<close> and from that the structured reference string (srs)/public key 
\<open>PK = (g, g^\<alpha>, ... , g^(\<alpha>^t))\<close>. Setup is a trusted Setup function, which generates the shared public 
key for both parties (prover and verifier).\<close>
definition Setup :: "('e mod_ring \<times> 'a list) spmf"
where 
  "Setup = do {
    x :: nat \<leftarrow> sample_uniform (order G\<^sub>p);
    let \<alpha>::'e mod_ring = of_int_mod_ring (int x) in
    return_spmf (\<alpha>, map (\<lambda>t. \<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> (\<alpha>^t)) [0..<max_deg+1]) 
  }"

text\<open>This function computes \<open>g^\<phi>(\<alpha>)\<close>, given the by Setup generated public key. 
(\<open>\<alpha>\<close> being the from Setup generated private key)

The function is basically a Prod of \<open>public key!i ^ coeff \<phi> i\<close>, which computes \<open>g^\<phi>(a)\<close>, given the 
public key:
\<open>\<Prod>[0...degree \<phi>]. PK!i^coeff \<phi> i\<close> 
= \<open>\<Prod>[0...degree \<phi>]. g^(\<alpha>^i)^coeff \<phi> i\<close>
= \<open>\<Prod>[0...degree \<phi>]. g^(coeff \<phi> i * \<alpha>^i)\<close>
= \<open>g^(\<Sum>[0...degree \<phi>]. coeff \<phi> i * \<alpha>^i)\<close>
= \<open>g^\<phi>(\<alpha>)\<close>
\<close>
fun g_pow_PK_Prod :: "'a list \<Rightarrow>'e mod_ring poly \<Rightarrow> 'a" where
  "g_pow_PK_Prod PK \<phi> = fold (\<lambda>i acc. acc \<otimes>\<^bsub>G\<^sub>p\<^esub> PK!i ^\<^bsub>G\<^sub>p\<^esub> (poly.coeff \<phi> i)) [0..<Suc (degree \<phi>)] \<one>\<^bsub>G\<^sub>p\<^esub>"

text \<open>q\_coeffs is a accumulator for the fold function.
fold coeffs\_n creates a vertical summation by going through the power\_diff\_sumr2 and instead of 
adding the horizontal row, mapping it into a list, which is added onto the previous list of 
coefficients, hence summing the coefficients vertical in a list. Illustration:

0: [0                     ]  
=> map (+)
1: [f1                    ]
=> map(+)
2: [f1 + f2*u             , f2*x        ] 
=> map(+)
3: [f1 + f2*u + f3*u\textasciicircum{}2    , f2*x+f3*u*x , f3*x\textasciicircum{}2]
...
n: [f1 + ... + fn*u\textasciicircum{}(n-1) , ... , f(i-1)*x\textasciicircum{}i +...+fn*u\textasciicircum{}((n-1)-i)*x\textasciicircum{}i , ... , fn*x\textasciicircum{}(n-1)]

Hence the resulting list represents the vertical sum with coefficient i at position (i-1).
The correctness proof is to be found in the correctness theory KZG\_correct.
\<close>
definition coeffs_n :: "'e mod_ring poly \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring list \<Rightarrow> nat \<Rightarrow> 'e mod_ring list"
  where "coeffs_n \<phi> u = (\<lambda>q_coeffs. \<lambda>n. map (\<lambda>(i::nat). (nth_default 0 q_coeffs i + poly.coeff \<phi> n * u ^ (n - Suc i))) [0..<n])"

text \<open>The objective of this function is to extract \<open>\<psi>\<close> in \<open>\<phi> x - \<phi> u = (x-u) * \<psi> x\<close>
Idea:
the polynomial \<open>\<phi>\<close> can be represented as a sum, hence:
\<open>\<phi> x - \<phi> u\<close>
= \<open>(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i) - (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * x^i)\<close>
= \<open>(x-u)(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j))\<close>
(for the last step see the lemma power\_diff\_sumr2)
Hence: \<open>\<psi> x = (\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j))\<close>
However, to build a polynomial \<open>\<psi>\<close> in Isabelle, we need the individual coefficients for every power 
of x (i.e. bring the sum into a form of \<open>(\<Sum>i\<le>degree \<phi>. coeff_i*x^i)\<close> where coeff\_i is the individual
coefficients for every power i of x. This translation is the main-purpose of the extractor function. 
The key idea is reordering the summation obtained from the power\_diff\_sumr2 lemma:

One can imagine the summation of power\_diff\_sumr2 to be horizontal, in the sense that it computes 
the coefficients from 0 to degree \<open>\<phi>\<close> = n, and adds (or could add) to each coefficient in every iteration:
0: 0 +
1: f1 +
2: f2*u + f2*x +
3: f3*u\textasciicircum{}2 + f3*u*x + f3*x\textasciicircum{}2
...
n: fn*u\textasciicircum{}(n-1) + ... fn*u\textasciicircum{}((n-1)-i)*x\textasciicircum{}i ...  + fn*x\textasciicircum{}(n-1)
we order it to compute the coefficients one by one (to compute vertical)
1: 0 + f1          + ... + fn*u\textasciicircum{}(n-1)         +
2: 0 + f2 * x      + ... + fn*u\textasciicircum{}((n-1)-1) * x +
...
n: 0 + fn * x\textasciicircum{}(n-1)

In formulas:
\<open>(\<Sum>i\<le>degree \<phi>. coeff \<phi> i * (\<Sum>j<i. u^(i - Suc j)*x^j))\<close> =
\<open>(\<Sum>i\<le>degree \<phi>. (\<Sum>j\<in>{i<..<Suc (degree \<phi>)}. coeff \<phi> j * u^(j-Suc i)) * x^i)\<close>
\<close>
definition \<psi>_of :: "'e mod_ring poly \<Rightarrow> 'e mod_ring \<Rightarrow> 'e mod_ring poly" 
  where "\<psi>_of \<phi> u = (let 
     \<psi>_coeffs = foldl (coeffs_n \<phi> u) [] [0..<Suc (degree \<phi>)] \<comment>\<open>coefficients of \<open>\<psi>\<close>\<close>
    in Poly \<psi>_coeffs) \<comment>\<open>\<open>\<psi>\<close>\<close>"

text \<open>a wrapper around Setup that hands the srs to both parties\<close>
definition key_gen :: "('a ck \<times> 'a vk) spmf"
  where "key_gen =  do {
    (\<alpha>, PK) \<leftarrow> Setup;
    return_spmf (PK,PK) 
  }"

text \<open>the KZG functions follow the description in section 3.2 of the KZG paper, but mirror the 
structure and naming of the abstract polynomial commitment scheme.\<close>

definition commit :: "'a ck \<Rightarrow> 'e mod_ring poly \<Rightarrow> ('a commit \<times> trapdoor) spmf"
  where "commit PK \<phi> = return_spmf (g_pow_PK_Prod PK \<phi>, ()) \<comment>\<open>\<open>g^\<phi>(\<alpha>)\<close>\<close>"

definition verify_poly :: "'a vk \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'a commit \<Rightarrow> trapdoor \<Rightarrow> bool"
  where "verify_poly PK \<phi> C td = (C = g_pow_PK_Prod PK \<phi>)  \<comment>\<open>\<open>C = g^\<phi>(\<alpha>)\<close>\<close>"

text \<open>This is the createWitness function in the KZG paper\<close>
definition Eval :: "'a ck \<Rightarrow> trapdoor \<Rightarrow> 'e mod_ring poly \<Rightarrow> 'e mod_ring \<Rightarrow> ('e mod_ring \<times> 'a witness)"
  where "Eval PK td \<phi> i = (let \<psi> = \<psi>_of \<phi> i \<comment>\<open>\<open>\<psi>\<close> in \<open>\<phi>(x) - \<phi>(i) = (x-i) * \<psi>(x)\<close>\<close>
    in (poly \<phi> i, g_pow_PK_Prod PK \<psi>) \<comment>\<open>\<open>(\<phi>(i),g^\<psi>(\<alpha>))\<close>\<close>)"

definition verify_eval :: "'a vk \<Rightarrow> 'a commit \<Rightarrow> 'e mod_ring \<Rightarrow> ('e mod_ring \<times> 'a witness) \<Rightarrow> bool"
  where "verify_eval PK C i val = (let (eval,w) = val 
  in  (e w (PK!1  \<div>\<^bsub>G\<^sub>p\<^esub> (\<^bold>g\<^bsub>G\<^sub>p\<^esub> ^\<^bsub>G\<^sub>p\<^esub> i)) \<otimes>\<^bsub>G\<^sub>T\<^esub> ((e \<^bold>g\<^bsub>G\<^sub>p\<^esub> \<^bold>g\<^bsub>G\<^sub>p\<^esub>) ^\<^bsub>G\<^sub>T\<^esub> eval) = e C \<^bold>g\<^bsub>G\<^sub>p\<^esub>)) 
    \<comment>\<open>\<open>e(g^\<psi>(\<alpha>), g^\<alpha> / g^i) \<otimes> e(g,g)^\<phi>(i) = e(C, g)\<close>\<close>"

definition valid_poly::"'e mod_ring poly \<Rightarrow> bool"
  where "valid_poly \<phi> = (degree \<phi> \<le> max_deg)"

definition valid_argument :: "'e argument \<Rightarrow> bool"
  where "valid_argument _ = True"

definition valid_eval::"('e mod_ring \<times> 'a witness) \<Rightarrow> bool"
  where "valid_eval val = (let (_,w) = val in w \<in> carrier G\<^sub>p)"

text \<open>the KZG is a polynomial commitment scheme\<close>
sublocale abstract_polynomial_commitment_scheme key_gen commit verify_poly Eval verify_eval 
  valid_poly valid_argument valid_eval .

end

end