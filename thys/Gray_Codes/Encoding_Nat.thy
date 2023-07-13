(*
  Author: Maximilian Spitz
*)


section \<open>An Encoding for Natural Numbers\<close>

theory Encoding_Nat
  imports Main
begin

text \<open>
At first, an encoding of naturals as lists of digits with respect to
  an arbitrary base $b \geq 2$ is introduced because the presented
  Gray code and its properties are reasonably expressed in terms of
  a word representation of numbers.
\<close>


subsection \<open>Validity and Valuation\<close>

text \<open>
In the context of a given base, not all possible code words are valid
  number representations.
A validity predicate is defined, that checks if a code word is valid
  and a valuation to obtain the number represented by a valid word.
\<close>

type_synonym base = nat

type_synonym word = "nat list"

fun val :: "base \<Rightarrow> word \<Rightarrow> nat" where
  "val b [] = 0"
| "val b (a#w) = a + b*val b w"

fun valid :: "base \<Rightarrow> word \<Rightarrow> bool" where
  "valid b [] \<longleftrightarrow> 2\<le>b"
| "valid b (a#w) \<longleftrightarrow> a<b \<and> valid b w"

text \<open>Given a base, the value of a valid word is bound by its length.\<close>

lemma val_bound:
  "valid b w \<Longrightarrow> val b w < b^length(w)"
proof (induction w)
  case Nil thus ?case by simp
next
  case (Cons a w)
  hence IH: "1+val b w \<le> b^length(w)" by simp
  have "val b (a#w) < b*(1+val b w)" using Cons.prems by auto
  also have "... \<le> b*b^length(w)" using IH mult_le_mono2 by blast
  also have "... = b^length(a#w)" by simp
  finally show ?case by blast
qed

lemma valid_base:
  "valid b w \<Longrightarrow> 2\<le>b"
  by (induction w) auto


subsection \<open>Encoding Numbers as Words\<close>

text \<open>
It was stated that not all code words are valid. Similarly, numbers do not
  have a unique word representation in general.
Therefore, it is reasonable to normalise representations with respect
  to either value or word length.
A normal representation w.r.t. value is without leading zeroes.
However, if the word length is fixed, numbers can be represented
  only up to an upper bound. Note that this bound is stated above.
\<close>

fun enc :: "base \<Rightarrow> nat \<Rightarrow> word" where
  "enc _ 0 = []"
| "enc b n = (if 2\<le>b then n mod b#enc b (n div b) else undefined)"

fun enc_len :: "base \<Rightarrow> nat \<Rightarrow> nat" where
  "enc_len _ 0 = 0"
| "enc_len b n = (if 2\<le>b then Suc(enc_len b (n div b)) else undefined)"

fun lenc :: "nat \<Rightarrow> base \<Rightarrow> nat \<Rightarrow> word" where
  "lenc 0 _ _ = []"
| "lenc (Suc k) b n = n mod b#lenc k b (n div b)"

definition normal :: "base \<Rightarrow> word \<Rightarrow> bool" where
  "normal b w \<equiv> enc_len b (val b w) = length w"


subsection \<open>Correctness\<close>

text \<open>
Now, the expected properties of above definitions are proven as well as
  that they interact correctly.
\<close>

lemma length_enc:
  "2\<le>b \<Longrightarrow> length (enc b n) = enc_len b n"
  by (induction b n rule: enc_len.induct) auto

lemma length_lenc:
  "length (lenc k b n) = k"
  by (induction k arbitrary: n) auto

lemma val_correct:
  "valid b w \<Longrightarrow> lenc (length w) b (val b w) = w"
  by (induction w) auto

lemma val_enc:
  "2\<le>b \<Longrightarrow> val b (enc b n) = n"
  by (induction b n rule: enc.induct) auto

lemma val_lenc:
  "val b (lenc k b n) = n mod b^k"
  apply (induction k arbitrary: n)
  by (auto simp add: mod_mult2_eq)

lemma valid_enc:
  "2\<le>b \<Longrightarrow> valid b (enc b n)"
  by (induction b n rule: enc.induct) auto

lemma valid_lenc:
  "2\<le>b \<Longrightarrow> valid b (lenc k b n)"
  by (induction k arbitrary: n) auto

lemma encodings_agree:
  "2\<le>b \<Longrightarrow> lenc (enc_len b n) b n = enc b n"
  by (metis length_enc val_correct val_enc valid_enc)

lemma inj_enc:
  "2\<le>b \<Longrightarrow> inj (enc b)"
  by (metis val_enc injI)

lemma inj_lenc:
  "inj_on (lenc k b) {..<b^k}"
proof (rule inj_on_inverseI)
  fix n :: nat
  assume "n \<in> {..<b^k}"
  thus "val b (lenc k b n) = n" by (simp add: val_lenc)
qed

lemma normal_enc:
  "2\<le>b \<Longrightarrow> normal b (enc b n)"
  by (simp add: length_enc normal_def val_enc)

lemma normal_eq:
  "\<lbrakk>valid b v; valid b w; normal b v; normal b w; val b v = val b w\<rbrakk> \<Longrightarrow> v = w"
  by (metis normal_def val_correct)

lemma inj_val:
  "inj_on (val b) {w. valid b w \<and> normal b w}"
proof (rule inj_onI)
  fix u v :: word
  assume 1: "val b u = val b v"
  assume "u \<in> {w. valid b w \<and> normal b w}"
     and "v \<in> {w. valid b w \<and> normal b w}"
  hence "valid b u \<and> normal b u \<and> valid b v \<and> normal b v" by blast
  with "1" show "u = v" using normal_eq by blast
qed

lemma enc_val:
  "\<lbrakk>valid b w; normal b w\<rbrakk> \<Longrightarrow> enc b (val b w) = w"
  by (metis encodings_agree normal_def val_correct valid_base)

lemma range_enc:
  "2\<le>b \<Longrightarrow> range (enc b) = {w. valid b w \<and> normal b w}"
proof
  show "2\<le>b \<Longrightarrow> range (enc b) \<subseteq> {w. valid b w \<and> normal b w}"
    by (simp add: image_subsetI normal_enc valid_enc)
next
  assume "2\<le>b"
  show "{w. valid b w \<and> normal b w} \<subseteq> range (enc b)"
  proof
    fix v :: word
    assume "v \<in> {w. valid b w \<and> normal b w}"
    hence "valid b v \<and> normal b v" by blast
    hence "enc b (val b v) = v" by (simp add: enc_val)
    thus "v \<in> range (enc b)" by (metis rangeI)
  qed
qed

lemma range_lenc:
  "2\<le>b \<Longrightarrow> lenc k b ` {..<b ^ k} = {w. valid b w \<and> length w = k}"
proof
  show "2 \<le> b \<Longrightarrow> lenc k b ` {..<b ^ k} \<subseteq> {w. valid b w \<and> length w = k}"
    by (simp add: image_subsetI length_lenc valid_lenc)
next
  assume "2\<le>b"
  show "{w. valid b w \<and> length w = k} \<subseteq> lenc k b ` {..<b ^ k}"
  proof
    fix v :: word
    let ?v = "val b v"
    assume "v \<in> {w. valid b w \<and> length w = k}"
    hence 1: "valid b v \<and> length v = k" by blast
    hence "?v < b^k" using val_bound by blast
    hence "?v \<in> {..<b^k}" by blast
    from "1" have "lenc k b ?v = v" using val_correct by blast
    thus "v \<in> lenc k b ` {..<b ^ k}" by (metis \<open>?v \<in> {..<b^k}\<close> image_eqI)
  qed
qed

theorem enc_correct:
  "2\<le>b \<Longrightarrow> bij_betw (enc b) UNIV {w. valid b w \<and> normal b w}"
  by (simp add: bij_betw_def inj_enc range_enc)

text \<open>
Given a valid base $b$ and length $k$, we encode exactly the first $b^k$ numbers.
\<close>

theorem lenc_correct:
  "2\<le>b \<Longrightarrow> bij_betw (lenc k b) {..<b^k} {w. valid b w \<and> length w = k}"
  by (simp add: bij_betw_def inj_lenc range_lenc)


subsection \<open>Circular Increment Operation\<close>

text \<open>
It is beneficial for our purpose to have an increment operation on
  words of fixed length that wraps around.
Mathematically, this corresponds to adding 1 in the additive group
  of the factor ring of the integers modulo ($b^k$).
Correctness is proven in terms of previously verified operations.
\<close>

fun inc :: "nat \<Rightarrow> word \<Rightarrow> word" where
  "inc _ [] = []"
| "inc b (a#w) = Suc a mod b#(if Suc a \<noteq> b then w else inc b w)"

lemma length_inc:
  "length (inc b w) = length w"
  by (induction w) auto

lemma valid_inc:
  "valid b w \<Longrightarrow> valid b (inc b w)"
  by (induction w) auto

text \<open>
Note that the following fact shows that we do not only have an encoding
  in the sense that it is a bijection but we also preserve a certain structure,
  that is necessary for the purpose of reasoning about Gray codes.
\<close>

theorem val_inc:
  "valid b w \<Longrightarrow> val b (inc b w) = Suc (val b w) mod b^length(w)"
proof (induction w)
  case Nil thus ?case by simp
next
  case (Cons a w)
  hence IH: "val b (inc b w) = Suc(val b w) mod b^length(w)" by simp
  show ?case
  proof cases
    assume 1: "Suc a = b"
    hence "val b (inc b (a#w)) = b*val b (inc b w)" by simp
    also have "... = b*(Suc(val b w) mod b^length w)" using IH by simp
    also have "... = b*Suc(val b w) mod (b*b^length w)" using mult_mod_right by blast
    also have "... = (Suc a + b*val b w) mod (b^length(a#w))" by (simp add: "1")
    also have "... = Suc(val b (a # w)) mod (b^length(a#w))" by simp
    finally show ?thesis by blast
  next
    let ?v = "Suc a + b*val b w"
    assume 2: "Suc a \<noteq> b"
    with Cons.prems have "valid b (inc b (a#w))" by simp
    hence "val b (inc b (a#w)) < b^length(inc b (a#w))" using val_bound by blast
    hence "val b (inc b (a#w)) < b^length(a#w)" using length_inc by metis
    hence "?v < b^length(a#w)" using "2" Cons.prems by simp
    hence "?v = ?v mod b^length(a#w)" by simp
    thus ?thesis using "2" Cons.prems by auto
  qed
qed

lemma inc_correct:
  "inc b (lenc k b n) = lenc k b (Suc n)"
  apply (induction k arbitrary: n)
  by (auto simp add: div_Suc mod_Suc)

lemma inc_not_eq: "valid b w \<Longrightarrow> (inc b w = w) = (w = [])"
  by (induction w) auto

end
