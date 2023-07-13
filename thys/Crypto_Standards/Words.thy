theory Words
  imports  
    More_Bit_Operations_Nat    
    "HOL.Transcendental" 
    "HOL-Number_Theory.Residues"
begin

text \<open>This theory implements the conversion from non-negative integers to a string of "octets"
(eight-bit bytes) and back again as defined in PKCS #1 v2.2.  Moreover, this theory generalizes
these conversions to be between non-negative integers and w-bit words.  The following is an excerpt
from the standard where we have replaced "octet" with "word" and any instance of 8 with w:

"Two data conversion primitives are employed in the schemes defined in this document:
  •I2OSP – Integer-to-Word-String primitive
  •OS2IP – Word-String-to-Integer primitive
For the purposes of this document, and consistent with ASN.1 syntax, a word string is an ordered
sequence of words (w-bit values).  The sequence is indexed from first (conventionally,
leftmost) to last (rightmost).  For purposes of conversion to and from integers, the first word
is considered the most significant in the following conversion primitives.

I2OSP – Integer-to-Word-String primitive:

Write the integer x in its unique xLen-digit representation in base (2^w):
  x = x_{xLen–1} (2^w)^{xLen–1} + x_{xLen–2} (2^w)^{xLen–2} + ... + x_1 (2^w) + x_0,  
where 0 \<le> x_i < (2^w) (note that one or more leading digits will be zero if x is less than 
(2^w)^{xLen–1}). 

Let the word X_i have the integer value x_{xLen–i} for 1 \<le> i \<le>xLen.  Output the word string 
  X = X_1 X_2 ... X_{xLen}. 

OS2IP – Word-String-to-Integer primitive:

Let X_1 X_2 ...X_{xLen} be the words of X from first to last, and let x_{xLen–i} be the integer 
value of the word X_i for 1 \<le> i \<le> xLen.  Let 
  x = x_{xLen–1} (2^w)^{xLen–1} + x_{xLen–2} (2^w)^{xLen–2} + ... + x_1 (2^w) + x_0. 
Output x."

For this theory, we want to be agnostic to the variable type that might be used to store the word
in any particular implementation of the standard.  Thus we concern ourselves only with the (non-
negative) integer value of the words.  Thus our words are nats and our word strings are lists
of nats.  Then for a w-bit word to be valid, it must be less than (2^w).

Also, the standard only has an opinion about what I2OSP should be when the input x can be written
in xLen or fewer words.  We are not constrained by the standard when defining nat_to_words_len
when x is too large.  We choose to define nat_to_words_len so that it converts the natural number
x to as many words as required, even if it is more than xLen.  The other choice would be to
truncate the list of words at xLen.  Either choice is valid and only affects the sorts of lemmas
we must prove.
\<close>

type_synonym words = "nat list"

lemma n_div_2tow_cases:
  assumes zero: "(n::nat) = 0 \<Longrightarrow> R"
  and     div : "\<lbrakk> n div 2^w < n ; 0 < n \<rbrakk> \<Longrightarrow> R"
  and     wpos: "0 < w"
  shows         "R"
proof (cases "n = 0")
  assume "n = 0"
  thus R by (rule zero)
next
  assume "n \<noteq> 0"
  hence "0 < n" by simp
  hence "n div 2^w < n" 
    by (metis wpos One_nat_def Suc_leI div_less_dividend le_less_trans less_exp) 
  from this and \<open>0 < n\<close> show R by (rule div)
qed

section\<open>Words Valid\<close>
text \<open>A nat is a valid w-bit word exactly when it is < 2^w.  So a list of nats is valid when all
the elements are < 2^w.\<close>

definition words_valid :: "nat \<Rightarrow> words \<Rightarrow> bool" where
  "words_valid w os = (\<forall>b\<in>set os. b < 2^w)"

lemma words_valid_nil: "words_valid w []"
  using words_valid_def by force

lemma words_valid_zeros: "words_valid w (replicate n 0)"
  using words_valid_def by simp

lemma words_valid_concat:
  assumes "words_valid w a" "words_valid w b"
  shows   "words_valid w (a @ b)"
  using assms words_valid_def by fastforce

lemma words_valid_cons:
  assumes "words_valid w as" "a < 2^w"
  shows   "words_valid w (a # as)"
  using assms words_valid_def by auto

lemma words_valid_trunc:
  assumes "words_valid w (as @ bs)"
  shows   "words_valid w as \<and> words_valid w bs"
  using assms words_valid_def by force
  
lemma words_valid_take:
  assumes "words_valid w as"
  shows   "words_valid w (take n as)"
  by (metis append_take_drop_id assms words_valid_trunc)

lemma words_valid_drop:
  assumes "words_valid w as"
  shows   "words_valid w (drop n as)"
  by (meson assms in_set_dropD words_valid_def)

lemma words_valid_hd:
  assumes "words_valid w as" "as \<noteq> []"
  shows   "(hd as) < 2^w"
  using assms list.set_sel(1) words_valid_def by blast

lemma words_valid_tl:
  assumes "words_valid w as"
  shows   "words_valid w (tl as)"
  by (metis (no_types) assms drop0 drop_Suc words_valid_drop)

lemma words_valid_last:
  assumes "words_valid w as" "as \<noteq> []"
  shows   "last as < 2^w"
  using assms last_in_set words_valid_def by blast 

lemma words_valid_butlast:
  assumes "words_valid w as"
  shows   "words_valid w (butlast as)"
  by (meson assms words_valid_def in_set_butlastD) 

lemma words_valid_ith:
  assumes "words_valid w as" "i < length as"
  shows   "as ! i < 2^w"
  using assms nth_mem words_valid_def by blast

text \<open>In FIPS 180-4, addition is done modulo the wordsize. The following is convenient to have.\<close>
lemma words_valid_sum_mod: "words_valid w (map2 (\<lambda>x y. (x+y) mod (2^w)) X Y)"
proof (induct "length (map2 (\<lambda>x y. (x+y) mod (2^w)) X Y)" arbitrary: X Y)
  case 0
then show ?case by (metis length_0_conv words_valid_nil)
next
  case C: (Suc xa)
  let ?Z = "map2 (\<lambda>x y. (x+y) mod (2^w)) X Y"
  let ?hZ = "hd ?Z"
  let ?tZ = "tl ?Z"
  have 1: "?hZ = ((hd X) + (hd Y)) mod 2^w"
    by (metis (no_types, lifting) Nil_is_map_conv C.hyps(2) hd_zip length_0_conv list.map_sel(1) 
        nat.simps(3) prod.simps(2) zip_eq_Nil_iff)
  have 2: "?hZ < 2^w"         using 1 by simp
  have 3: "length ?tZ = xa"   using C(2) by auto
  have 4: "?Z = ?hZ # ?tZ"    by (metis C(2) list.exhaust_sel list.size(3) old.nat.distinct(1)) 
  have 5: "?tZ = map2 (\<lambda>x y. (x+y) mod (2^w)) (tl X) (tl Y)"
    by (smt (z3) 4 Nil_is_map_conv list.exhaust_sel list.sel(3) map_tl zip_Cons_Cons
            zip_eq_Nil_iff) 
  have 6: "words_valid w ?tZ" by (metis C(1) 3 5) 
  show ?case by (metis 2 4 6 words_valid_cons)
qed


section\<open>Strip Words\<close>
text\<open>In the PKCS #1 standard, we sometimes pad a word string with 0s and sometimes with non-0s.
Then when decoding, we must strip an word string of leading 0s (resp. non-0s).\<close>

fun words_strip_zero    :: "words \<Rightarrow> words" where
   "words_strip_zero [] = []"
|  "words_strip_zero os = (if (hd os = 0) then words_strip_zero (tl os) else os)"

fun words_strip_nonzero :: "words \<Rightarrow> words" where
  "words_strip_nonzero [] = []"
| "words_strip_nonzero os = (if (hd os = 0) then os else words_strip_nonzero (tl os) )"

lemma strip_prepend_zeros: "words_strip_zero ((replicate x 0) @ bs) = words_strip_zero bs"
  apply (induction x)  by auto

lemma strip_zero_length: "length (words_strip_zero bs) \<le> length bs"
  apply (induction bs) by auto

lemma strip_zero_leading_zeros:
  assumes "ls = length (words_strip_zero bs)"  "lb = length bs"
  shows   "\<forall>i < (lb - ls). bs ! i = 0"
proof -
  let ?l = "lb - ls"
  show ?thesis using assms proof (induction ?l arbitrary: bs lb ls)
  case 0
  then show ?case by fastforce 
next
  case 1: (Suc l)  
  let ?h = "hd bs"
  let ?t = "tl bs"
  let ?s = "words_strip_zero bs" 
  have 3: "lb = l + 1 + ls"           using 1(2) by simp 
  have 4: "0 < lb"                    using 1(2) by simp
  have 5: "bs = ?h # ?t"              using 1(4) 4 by fastforce 
  have 6: "?h = 0" 
    by (metis 1(2,3,4) 5 Zero_not_Suc cancel_comm_monoid_add_class.diff_cancel 
              words_strip_zero.simps(2))
  have 7: "?s = words_strip_zero ?t"  using 5 6 words_strip_zero.simps(2) by metis
  show ?case
    by (metis 1(1,2,3,4) 5 6 7 cancel_ab_semigroup_add_class.diff_right_commute diff_Suc_1 
              length_tl less_Suc_eq_0_disj nth_Cons')
  qed
qed

lemma strip_zero_head: 
  assumes "words_strip_zero bs \<noteq> []" 
  shows   "0 < (words_strip_zero bs) ! 0" 
using assms proof (induction bs)
  case Nil 
  then show ?case using words_strip_zero.simps(1) by blast
next
  case (Cons a bs)
  then show ?case by auto 
qed

lemma strip_zero_drop:
  "words_strip_zero bs = drop ((length bs) - (length (words_strip_zero bs))) bs"
proof (induction bs)
  case Nil
  then show ?case by force
next
  case (Cons a bs)
  then show ?case
    by (metis (no_types, opaque_lifting) add.right_neutral add_Suc_right add_diff_cancel_left' 
              diff_le_self drop_Cons' le_add_diff_inverse length_Cons length_drop list.sel(3) 
              nat.simps(3) words_strip_zero.simps(2)) 
qed 

lemma strip_zero_concat:
  assumes "bl = length bs" "s = words_strip_zero bs" "sl = length s" "z = (replicate (bl-sl) 0)"
  shows   "bs = z @ s"
  by (metis append_take_drop_id assms diff_le_self le_eq_less_or_eq length_replicate 
            nth_replicate nth_take_lemma strip_zero_drop strip_zero_leading_zeros take_all)

lemma strip_non0_nil: "words_strip_nonzero [] = []"
  by simp

lemma strip_non0_nil2:
  assumes "words_strip_nonzero as = []"
  shows   "\<forall>a \<in> set as. 0 < a" 
using assms proof (induct as)
  case Nil
  then show ?case by force
next
  case (Cons a as)
  then show ?case
    by (metis list.distinct(1) list.sel(1) list.sel(3) neq0_conv 
           words_strip_nonzero.simps(2) set_ConsD) 
qed

lemma strip_non0_nil3:
  assumes "\<forall>a \<in> set as. 0 < a"
  shows   "words_strip_nonzero as = []"
using assms proof (induct as)
case Nil
then show ?case by auto
next
  case (Cons a as)
  then show ?case by simp
qed
  
lemma strip_non0_cons:
  assumes "0 < a"
  shows   "words_strip_nonzero (a # as) = words_strip_nonzero as"
  using assms by auto

lemma strip_non0_cons2: "words_strip_nonzero (0 # as) = (0 # as)"
  by simp

lemma strip_non0_concat1: 
  assumes "words_strip_nonzero as \<noteq> []" 
  shows   "words_strip_nonzero (as @ bs) = (words_strip_nonzero as) @ bs"
using assms proof (induct as arbitrary: bs)
  case Nil
  then show ?case by force
next
  case (Cons a as)
  then show ?case by auto 
qed

lemma strip_non0_concat:
  assumes "\<forall>a \<in> set as. 0 < a"
  shows   "words_strip_nonzero (as @ [0] @ bs) = [0] @ bs"
using assms proof (induct as arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case I: (Cons a as)
  have 1: "0 < a" using I by simp
  have 2: "words_strip_nonzero (a # as @ [0] @ bs) =  words_strip_nonzero (as @ [0] @ bs)"
    using 1 strip_non0_cons by blast
  then show ?case using 2 I by auto
qed

lemma strip_non0_len:
  assumes "as = words_strip_nonzero bs" 
  shows   "(length as) \<le> (length bs)"
using assms proof (induct bs arbitrary: as)
  case Nil
  then show ?case by simp
next
  case (Cons a bs)
  then show ?case
    by force  
qed

lemma strip_non0_drop:
  "words_strip_nonzero bs = drop ((length bs) - (length (words_strip_nonzero bs))) bs"
proof (induction bs)
  case Nil
  then show ?case by fastforce
next
  case (Cons a bs)
  then show ?case
    using Suc_diff_le strip_non0_len by force 
qed

lemma strip_non0_head: 
  assumes "words_strip_nonzero bs \<noteq> []"
  shows   "(words_strip_nonzero bs) ! 0 = 0"
using assms proof (induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  then show ?case by force
qed
    
lemma strip_non0_idem: "words_strip_nonzero (words_strip_nonzero bs) = words_strip_nonzero bs"
  by (metis hd_conv_nth strip_non0_head strip_non0_nil words_strip_nonzero.elims)

lemma strip_non0_leading_pos:
  assumes "ls = length (words_strip_nonzero bs)"  "lb = length bs"
  shows   "\<forall>i < (lb - ls). 0 < bs ! i"
proof -
  let ?l = "lb - ls"
  show ?thesis using assms proof (induction ?l arbitrary: bs lb ls)
  case 0
  then show ?case by fastforce 
next
  case 1: (Suc l)  
  let ?h = "hd bs"
  let ?t = "tl bs"
  let ?s = "words_strip_nonzero bs" 
  have 3: "lb = l + 1 + ls"  using 1(2) by simp 
  have 4: "0 < lb"           using 1(2) by simp
  have 5: "bs = ?h # ?t"     using 1(4) 4 by fastforce 
  have 6: "0 < ?h" 
    by (metis 1(2,3,4) 5 Zero_not_Suc cancel_comm_monoid_add_class.diff_cancel 
              words_strip_nonzero.simps(2) gr0I)
  have 7: "?s = words_strip_nonzero ?t" by (metis strip_non0_cons 5 6) 
  show ?case
    by (metis 1(1,2,3,4) 5 6 7 cancel_ab_semigroup_add_class.diff_right_commute diff_Suc_1 
              length_tl less_Suc_eq_0_disj nth_Cons')
  qed
qed


section\<open>Nat to Words\<close>
text\<open>Convert any natural number to a word string.  Also, we define a function that converts a
natural number to a specified minimum number of words by padding with zeros if necessary.\<close>

function nat_to_words_rec :: "nat \<Rightarrow> nat \<Rightarrow> words \<Rightarrow> words" where
  "nat_to_words_rec w n nl = 
    (if w = 0 then nl else 
    (if n = 0 then nl
              else nat_to_words_rec w (n div (2^w)) ((n mod (2^w))#nl) ) )"
  by auto

termination nat_to_words_rec
  apply (relation "measure (\<lambda>(w, n, nl). n)") 
   apply auto
  using n_div_2tow_cases by blast 

definition nat_to_words :: "nat \<Rightarrow> nat \<Rightarrow> words" where
  "nat_to_words w n = nat_to_words_rec w n []" 

definition nat_to_words_len :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> words" where
  "nat_to_words_len w n len = 
    (let l = length (nat_to_words w n) in (replicate (len-l) 0) @ (nat_to_words w n))"

definition word_length :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "word_length w n = length (nat_to_words w n)"

lemma zero_to_word [simp]: "nat_to_words w 0 = []"
  by (simp add: nat_to_words_def)

lemma zero_to_words_len [simp]: "nat_to_words_len w 0 l = replicate l 0"
  using zero_to_word nat_to_words_len_def by auto

lemma nat_to_words_len_len: "l \<le> length (nat_to_words_len w n l)"
  by (simp add: nat_to_words_len_def)

lemma nat_to_zero_bit_words [simp]: "nat_to_words 0 n = []"
  by (simp add: nat_to_words_def)

lemma nat_to_zero_bit_words_len [simp]: "nat_to_words_len 0 n l = replicate l 0"
  by (simp add: nat_to_words_len_def)

lemma nat_to_zero_bit_words_len2 [simp]: "length (nat_to_words_len 0 n l) = l"
  by (simp add: nat_to_words_len_def)

lemma nat_to_zero_bit_word_len [simp]: "word_length 0 n = 0"
  by (simp add: word_length_def) 

lemma wpos:
  assumes "(n::nat) < 2^w" "0 < n"
  shows   "0 < w"
  using assms less_one by fastforce

lemma nat_to_one_word [simp]: 
  assumes "n < 2^w" "0 < n" 
  shows   "nat_to_words w n = [n]"
  using wpos assms nat_to_words_def by force

lemma nat_to_two_words:
  assumes "n < 2^(2*w)" "2^w \<le> n" 
  shows   "nat_to_words w n = [n div 2^w, n mod 2^w]" 
proof -
  have 0: "0 < w" using assms leD by fastforce 
  have 1: "n div 2^w < 2^w"
    by (metis assms(1) less_mult_imp_div_less power2_eq_square power_even_eq)  
  have 2: "0 < n div 2^w"   
    by (simp add: assms(2) div_greater_zero_iff) 
  have 3: "nat_to_words w n = nat_to_words_rec w (n div 2^w) [n mod 2^w]"
    by (metis 2 0 div_0 less_not_refl nat_to_words_def nat_to_words_rec.simps)
  show ?thesis using 0 1 2 3 by force
qed

lemma unfold_nat_to_words_rec: "nat_to_words_rec w n l = (nat_to_words_rec w n []) @ l" 
proof (cases "w=0")
  case True
  then show ?thesis by simp
next
  case False
  then have [simp]: "0 < w" by blast
  have "\<forall>l. nat_to_words_rec w n l = nat_to_words_rec w n [] @ l"
  proof (induct n rule: less_induct)
    fix m
    assume ind: "!!j. j < m \<Longrightarrow> \<forall> l. nat_to_words_rec w j l = nat_to_words_rec w j [] @ l"
    show "\<forall>l. nat_to_words_rec w m l = nat_to_words_rec w m [] @ l"
    proof
      fix l
      show "nat_to_words_rec w m l = nat_to_words_rec w m [] @ l"
      proof (cases "m < 0")
        assume "m < 0"
        thus ?thesis by blast
      next
        assume "~m < 0"
        show ?thesis 
        proof (rule n_div_2tow_cases [of m])
          assume [simp]: "m = 0"
          show ?thesis by simp
        next
          assume n2n: "m div 2^w < m"
          assume [simp]: "0 < m" 
          hence n20: "0 \<le> m div 2^w"
            by arith 
          from ind [of "m div 2^w"] and n2n n20
          have ind': "\<forall>l. nat_to_words_rec w (m div 2^w) l = nat_to_words_rec w (m div 2^w) [] @ l"
            by (meson \<open>0 < m\<close> div_less_dividend ind one_less_numeral_iff semiring_norm(76))
          show ?thesis
            by (metis (no_types) append.assoc append_Cons append_Nil ind' nat_to_words_rec.simps)
        next
          show "0 < w" by simp
        qed
      qed
    qed
  qed
  thus ?thesis ..
qed  

lemma nat_to_words_h:
  assumes "0 < n" "0 < w"
  shows   "nat_to_words w n = (nat_to_words w (n div 2^w))@[n mod 2^w]"
  by (metis assms nat_to_words_def nat_to_words_rec.simps neq0_conv unfold_nat_to_words_rec) 

lemma nat_to_words_len_h:
  assumes "0 < n" "0 < w"
  shows   "nat_to_words_len w n l = (nat_to_words_len w (n div 2^w) (l-1))@[n mod 2^w]"
  using assms nat_to_words_len_def nat_to_words_h by simp 

lemma nat_to_words_len_h2:
  assumes "0 < l" "0 < w" 
  shows   "nat_to_words_len w n l = (nat_to_words_len w (n div 2^w) (l-1))@[n mod 2^w]"
proof (cases "n=0")
  case True
  then show ?thesis
    by (metis Suc_pred' append_Nil2 assms(1) div_mult2_eq le_0_eq mod_less_eq_dividend 
          nat_mult_div_cancel_disj replicate.simps(2) replicate_app_Cons_same zero_to_words_len) 
next
  case False
  then show ?thesis by (meson assms(2) nat_to_words_len_h neq0_conv) 
qed

lemma nat_to_words_div_len: 
  assumes "0 < n" "0 < w" 
  shows   "length (nat_to_words w (n div 2^w)) + 1 = length (nat_to_words w n)" 
  using assms nat_to_words_h by force 

lemma nat_bnd_word_len:
  assumes "n < (2^w)^m" 
  shows   "length (nat_to_words w n) \<le> m"
proof (cases "w = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis using assms proof (induct m arbitrary: n w)
  case 0
  then have "n = 0" by simp 
  then show ?case   by auto
next
  case 1: (Suc m)
  then show ?case proof (cases)
    assume "n = 0"
    then show ?case by simp
  next
    assume "\<not> n = 0" 
    then have 2: "0 < n" by blast
    let ?nd = "n div 2^w"
    let ?nm = "n mod 2^w"
    have 3: "?nd < (2^w)^m"
      by (metis 1(3) less_mult_imp_div_less mult.commute power_Suc)
    have 4: "length (nat_to_words w ?nd) \<le> m" 
      using 1(1,2) 3 by fastforce 
    have 5: "nat_to_words w n = (nat_to_words w ?nd)@[?nm]" 
      using 2 nat_to_words_h 1(2) by blast
    show ?case by (simp add: 4 5)
    qed
  qed
qed

lemma nat_bnd_word_len2:
  assumes "n < (2^w)^m"  
  shows   "word_length w n \<le> m"
  using assms word_length_def nat_bnd_word_len by presburger

lemma nat_bnd_word_len_inv:
  assumes "m < length (nat_to_words w n)"  
  shows   "(2^w)^m \<le> n"
  using assms nat_bnd_word_len not_less by blast

lemma nat_bnd_word_len_inv2:
  assumes "m < word_length w n" 
  shows   "(2^w)^m \<le> n"
  using assms word_length_def nat_bnd_word_len_inv by simp

lemma nat_to_words_nil_iff_zero:
  assumes "0 < w"
  shows   "length (nat_to_words w n) = 0 \<longleftrightarrow> n = 0"
  using assms zero_to_word nat_to_words_h by fastforce 

lemma nat_to_words_nil_iff_zero2:
  assumes "0 < w"
  shows   "word_length w n = 0 \<longleftrightarrow> n = 0"
  using assms word_length_def nat_to_words_nil_iff_zero by presburger

lemma nat_lowbnd_word_len:
  assumes "(2^w)^m \<le> n"  "0 < w" 
  shows   "m < length (nat_to_words w n)"
using assms proof (induction m arbitrary: n)
  case 0
  then have "0 < n" by simp
  then show ?case   using assms(2) nat_to_words_nil_iff_zero by simp
next
  case 1: (Suc m)
  have 2: "0 < n"   using 1 by fastforce
  let ?d = "n div 2^w"
  let ?m = "n mod 2^w"
  have 3: "(2^w)^m \<le> ?d" 
    by (metis 1(2) div_greater_zero_iff div_mult2_eq power_Suc zero_less_numeral zero_less_power) 
  have 4: "m < length (nat_to_words w ?d)"              using 1(1) 3 assms(2) by blast
  have 5: "nat_to_words w n = (nat_to_words w ?d)@[?m]" using 2 nat_to_words_h assms(2) by blast
  show ?case  using 4 5 by force
qed

lemma nat_lowbnd_word_len2:
  assumes "(2^w)^m \<le> n"  "0 < w" 
  shows   "m < word_length w n"
  using assms word_length_def nat_lowbnd_word_len by presburger

lemma word_length_eq: 
  assumes "0 < n"  "0 < w" 
  shows   "(word_length w n = l) = ((n < ((2^w)^l)) \<and> (((2^w)^(l-1)) \<le> n))"
  by (smt (verit, ccfv_threshold) One_nat_def Suc_eq_plus1 Suc_leI add.commute assms diff_less 
  le_add_diff_inverse le_less less_le_trans nat_bnd_word_len2 nat_lowbnd_word_len2 not_le 
  power_0 zero_less_one)  

lemma word_length_eq2:
  assumes "word_length w n = l"  "0 < w"
  shows   "n < (2^w)^l"
  by (metis assms less_nat_zero_code nat_neq_iff word_length_eq zero_less_numeral zero_less_power)

lemma word_length_eq3:
  assumes "word_length w n = l"  "0 < n"  "0 < w" 
  shows   "(2^w)^(l-1) \<le> n"
  using assms word_length_eq by blast

lemma word_length_not2pow:
  assumes "word_length w n = l"  "0 < n"  "0 < w"  "\<not> (\<exists> m. n = 2^m)" 
  shows   "(2^w)^(l-1) < n"
  by (metis assms nat_less_le power_mult word_length_eq3)

lemma log2iffPow_h1:
  fixes n :: nat
  assumes "(log 2 n = \<lceil>log 2 n\<rceil>)"  "0 < n" 
  shows   "(\<exists> m. n = 2^m)"
proof - 
  let ?m = "nat \<lceil>log 2 n\<rceil>"
  have 0: "0 \<le> \<lceil>log 2 n\<rceil>"
    by (metis (no_types) assms(1,2) le_log2_of_power linorder_not_less of_int_0_le_iff 
              of_nat_less_0_iff order_le_less_trans power_mult word_length_eq3) 
  have 1: "\<lceil>log 2 n\<rceil> = real ?m"  using 0 by simp
  have 2: "log 2 n = real ?m"    using assms(1) 1 by presburger
  have 3: "n = 2 ^ ?m"
    by (metis (full_types) assms(2) 2 less_log2_of_power log2_of_power_less nat_neq_iff 
              of_nat_less_iff) 
  show ?thesis  using 3 by fast
qed

lemma log2iffPow_h2: 
  assumes "(\<exists> m. n = 2^m)"
  shows   "(log 2 n = \<lceil>log 2 n\<rceil>)"
  using assms by force 

lemma log2iffPow: 
  assumes "0 < (n::nat)"
  shows   "(log 2 n = \<lceil>log 2 n\<rceil>) = (\<exists> m. n = 2^m)"
  using assms log2iffPow_h1 by auto

lemma word_length_not2pow':
  assumes "word_length w n = l"  "0 < n"  "0 < w"  "log 2 n < \<lceil>log 2 n\<rceil>" 
  shows   "(2^w)^(l-1) < n"
  using assms log2iffPow[of n] word_length_not2pow[of w n l] by argo

lemma oddNotPow2:
  assumes "odd (n::nat)"  "1 < n"
  shows   "\<not> (\<exists> m. n = 2^m)"
  using assms(1,2) by fastforce

lemma oddLog2Ceil:
  assumes "odd (n::nat)"  "1 < n"
  shows   "(log 2 n) < \<lceil>(log 2 n)\<rceil>"
proof -
  have "log 2 n \<noteq> \<lceil>log 2 n\<rceil>"  using assms oddNotPow2 log2iffPow by simp
  then show ?thesis           by linarith
qed

lemma word_length_eq_odd:
  assumes "word_length w n = l" "0 < w" "odd n" "1 < n"
  shows   "(2^w)^(l-1) < n"
  by (metis assms bot_nat_0.not_eq_extremum dvd_power nat_less_le odd_pos power_0 
            word_length_not2pow)

text\<open>We can write the word_length as a function of the log base 2.  We only need that p is not a
power of two.  The lemmas for odd p or "p prime greater than 2" follow from this.\<close>
lemma wordLenLog2NotPow:
  assumes "0 < w"  "1 < p"  "(log 2 p) < \<lceil>(log 2 p)\<rceil>" 
  shows   "word_length w p = \<lceil>(log 2 p)/w\<rceil>" 
proof - 
  let ?l = "word_length w p"
  have r1: "p < (2^w)^?l"             using word_length_eq2 assms(1) by blast
  have r2: "p < 2^(w*?l)"             using r1 power_mult by metis
  have r3: "log 2 p < w*?l"           using r2 assms(2) log2_of_power_less by blast 
  have r4: "(log 2 p) / w < real(?l)" using r3 assms(1)
    by (simp add: mult.commute pos_divide_less_eq) 
  have l1: "(2^w)^(?l-1) < p"
    using assms(1,2,3) word_length_not2pow' by auto 
  have l2: "2^(w*(?l-1)) < p"         using l1 power_mult by metis
  have l3: "w*(?l-1) < log 2 p"       using l2 less_log2_of_power by fast
  have l4: "real (?l-1) < (log 2 p) / w"
    by (metis assms(1) l3 mult.commute mult_imp_less_div_pos of_nat_0_less_iff of_nat_mult) 
  show ?thesis                        using r4 l4 by linarith 
qed

lemma wordLenLog2Odd:
  assumes "odd p"  "1 < p"  "0 < w" 
  shows   "word_length w p = \<lceil>(log 2 p)/w\<rceil>"
  using assms(1,2,3) oddLog2Ceil wordLenLog2NotPow by blast 

lemma wordLenLog2Prime:
  assumes "prime p"  "2 < p"  "0 < w"
  shows   "word_length w p = \<lceil>(log 2 p)/w\<rceil>" 
  using assms(1,2,3) wordLenLog2Odd prime_gt_1_nat prime_odd_nat by blast

lemma nth_word: 
  assumes "i < length (nat_to_words w n)"  "0 < w"  
  shows   "(nat_to_words w n) ! ((length (nat_to_words w n))-1-i) = (n div (2^w)^i) mod (2^w)" 
using assms proof (induction i arbitrary: n w)
  case 0
  then show ?case proof (cases)
    assume "n = 0"
    then have "length (nat_to_words w n) = 0" using zero_to_word by blast
    then show ?thesis                         using 0 by blast
  next
    assume "\<not> n = 0"
    then have "0 < n"           by blast
    then have "nat_to_words w n = (nat_to_words w (n div (2^w)))@[n mod (2^w)]" 
      using nat_to_words_h 0(2) by blast
    then show ?thesis           by fastforce
  qed 
next
  case 1: (Suc i)
  let ?l = "length (nat_to_words w n)"
  let ?d = "n div (2^w)"
  let ?m = "n mod (2^w)"
  have 11: "1 < ?l"                                      using 1(2) by fastforce
  have 12: "0 < n"                                       using 11 nat_bnd_word_len_inv by force
  have 13: "nat_to_words w n = nat_to_words w ?d @ [?m]" using 12 1(3) nat_to_words_h by blast
  let ?ld = "length (nat_to_words w ?d)" 
  have 14: "?ld = ?l - 1"                                using 13 by fastforce
  have 15: "0 < ?ld"                                     using 14 11 by force
  have 16: "i < ?ld"                                     using 14 1(2) by linarith 
  have 17: "?ld - 1 - i = ?l - 1 - (Suc i)"              using 14 by fastforce
  have 18: "(nat_to_words w ?d) ! (?ld - 1 - i) = (?d div (2^w)^i) mod (2^w)" 
    using 1(1,3) 16 by blast
  have 19: "nat_to_words w n ! (?l - 1 - Suc i) = (nat_to_words w ?d) ! (?ld - 1 - i)"
    by (metis 13 14 15 17 diff_less nth_append zero_less_Suc) 
  have     "?d div (2^w)^i = n div (2^w)^(Suc i)" by (simp add: div_mult2_eq) 
  then show ?case  using 18 19 by argo
qed

lemma nth_word2: 
  assumes "j < length (nat_to_words w n)"  "0 < w"
  shows   "(nat_to_words w n) ! j = (n div (2^w)^(((length (nat_to_words w n))-1-j))) mod (2^w)"
  by (metis (no_types, lifting) One_nat_def Suc_pred add_diff_cancel_right' diff_less_Suc 
      le_add_diff_inverse le_eq_less_or_eq length_greater_0_conv less_Suc_eq list.size(3) 
      not_less_zero assms nth_word) 

lemma nth_word_len:
  assumes "i < length (nat_to_words_len w n l)"  "0 < w" 
  shows   "(nat_to_words_len w n l) ! ((length (nat_to_words_len w n l))-1-i) 
             = (n div (2^w)^i) mod (2^w)" 
proof (cases)
  assume "l \<le> word_length w n"
  then have "nat_to_words_len w n l = nat_to_words w n" 
    by (simp add: nat_to_words_len_def word_length_def)
  then show ?thesis  using assms nth_word by presburger
next
  assume "\<not> (l \<le> word_length w n)"
  then have 1: "word_length w n < l"  by simp
  let ?os = "nat_to_words w n"
  let ?ol = "length ?os"
  have 2: "?ol < l"                   using 1 word_length_def by auto 
  have 3: "nat_to_words_len w n l = (replicate (l-?ol) 0) @ (nat_to_words w n)" 
    using nat_to_words_len_def by presburger 
  then show ?thesis proof (cases)
    assume 4: "i < ?ol" 
    have "(nat_to_words_len w n l) ! ((length (nat_to_words_len w n l))-1-i) = 
               (nat_to_words w n)  ! ((length (nat_to_words w n))-1-i)"
      by (smt (z3) 2 3 4 One_nat_def Suc_pred add.commute assms diff_diff_cancel diff_right_commute
              le_add_diff_inverse length_append length_replicate less_imp_le_nat not_less_eq 
              nth_append zero_less_diff diff_diff_left) 
    then show ?thesis  using nth_word 4 assms(2) by presburger
  next
    assume 5: "\<not>(i < ?ol)"
    have 6: "(nat_to_words_len w n l) ! ((length (nat_to_words_len w n l))-1-i) = 0"
      by (metis 2 3 5 add.commute diff_Suc_eq_diff_pred diff_less_mono2 le_add_diff_inverse 
              length_append length_replicate less_imp_le_nat not_less_eq nth_append nth_replicate)
    have 7: "n div (2^w)^i = 0" by (meson 5 assms(2) div_less le_less_linear nat_lowbnd_word_len) 
    show ?thesis  using 6 7 by presburger 
  qed
qed

lemma nth_word2_len: 
  assumes "j < length (nat_to_words_len w n l)"  "0 < w"
  shows "(nat_to_words_len w n l) ! j = 
          (n div (2^w)^(((length (nat_to_words_len w n l))-1-j))) mod (2^w)"
  by (smt (z3) assms nth_word_len One_nat_def Suc_leI Suc_pred add_diff_cancel_right' diff_less_Suc
      le_add_diff_inverse length_greater_0_conv less_nat_zero_code list.size(3) not_le)
    
lemma words_upper_bound:
  assumes "os = nat_to_words w n"  "b \<in> set os" 
  shows   "b < (2^w)"
proof (cases "w = 0")
  case True
  then show ?thesis using assms by auto
next
  case False
  obtain i where 0: "b = os ! i \<and> 0 \<le> i \<and> i < length os" 
    by (metis le0 assms(2) in_set_conv_nth) 
  let ?l = "length os" 
  have "b = (n div (2^w)^(?l-1-i)) mod (2^w)"  using 0 nth_word2 assms(1) False by blast
  then show ?thesis  using mod_less_divisor False by simp
qed

lemma high_word_pos: 
  assumes "0 < n"  "0 < w" 
  shows   "0 < (nat_to_words w n) ! 0"
proof -
  let ?os = "nat_to_words w n"
  let ?l  = "length ?os" 
  have 1: "0 < ?l"             using assms nat_to_words_nil_iff_zero by auto 
  have 2: "(nat_to_words w n) ! 0 = ( n div (2^w)^(?l-1) ) mod (2^w)"
    using 1 nth_word2 assms(2) by auto
  have 3: "n < (2^w)^?l"       using word_length_def word_length_eq2 assms(2) by blast 
  have 4: "(2^w)^(?l-1) \<le> n"   using assms word_length_def word_length_eq by blast 
  have 5: "1 \<le> n div (2^w)^(?l-1)" 
    by (metis 4 bits_div_by_1 div_greater_zero_iff nat_neq_iff not_less_zero power_eq_0_iff 
         zero_neq_numeral) 
  have 6: "n div (2^w)^(?l-1) < (2^w)"
    by (metis 1 3 One_nat_def Suc_leI le_add_diff_inverse less_mult_imp_div_less power_add 
              power_one_right) 
  have 7: "( n div (2^w)^(?l-1) ) mod (2^w) = n div (2^w)^(?l-1)" using 5 6 by force
  show ?thesis   using 2 5 7 by linarith
qed

lemma high_word_pos2:
  assumes "0 < n"  "0 < w"
  shows   "0 < hd (nat_to_words w n)"
  by (metis assms high_word_pos hd_Cons_tl less_not_refl3 list.size(3) nat_to_words_nil_iff_zero2 
            nth_Cons_0 word_length_def) 

lemma nat_to_words_valid: "words_valid w (nat_to_words w n)"
  by (metis words_upper_bound words_valid_def)

lemma nat_to_words_valid_le:
  assumes "w1 \<le> w2"
  shows   "words_valid w2 (nat_to_words w1 n)"
  by (smt (z3) assms le_less_trans linorder_not_less nat_power_less_imp_less nat_to_words_valid 
      numeral_2_eq_2 words_valid_def zero_less_Suc)

lemma nat_to_words_len_lowbnd: 
  assumes "(2^w)^l \<le> n"  "0 < w" 
  shows   "nat_to_words_len w n l = nat_to_words w n"
  by (simp add: assms less_imp_le_nat nat_lowbnd_word_len nat_to_words_len_def)

lemma nat_to_words_len_upbnd:
  assumes "n < (2^w)^l" 
  shows   "length (nat_to_words_len w n l) = l"
  using assms nat_bnd_word_len nat_to_words_len_def by fastforce

lemma word_len_mono:
  assumes "a \<le> b"
  shows   "word_length w a \<le> word_length w b"
  by (metis assms gr_implies_not0 le_less_trans nat_bnd_word_len2 
            nat_to_zero_bit_word_len not_le not_less_iff_gr_or_eq word_length_eq2)

lemma nat_to_word_len_mono:
  assumes "a < b"
  shows   "length (nat_to_words_len w a l) \<le> length (nat_to_words_len w b l)"
  by (smt (z3) assms diff_Suc_1 le_eq_less_or_eq le_less_trans nat_bnd_word_len 
           nat_to_words_len_len nat_to_words_len_lowbnd nat_to_words_len_upbnd 
           nat_to_zero_bit_words_len2 neq0_conv not_le word_length_def word_length_eq2)

lemma nat_to_word_len_mono':
  assumes "a < b"  "word_length w b = l"  "0 < w"  
  shows   "length (nat_to_words_len w a l) = l"
  by (metis assms less_imp_le_nat nat_to_words_len_upbnd order_le_less_trans word_length_eq2)

lemma nat_to_words_len_valid: "words_valid w (nat_to_words_len w n l)"
  using nat_to_words_len_def nat_to_words_valid words_valid_concat words_valid_zeros by presburger

lemma sum_to_words:
  assumes "y < (2^w)^l"  "0 < x"  "0 < w"
  shows   "nat_to_words w (x*((2^w)^l) + y) = (nat_to_words w x) @ (nat_to_words_len w y l)"
using assms proof (induction l arbitrary: y)
  case 0
  then show ?case by force 
next
  case C: (Suc l)
  let ?yd = "y div (2^w)"
  let ?ym = "y mod (2^w)"
  have 1: "?yd < (2 ^ w) ^ l" by (metis C(2) less_mult_imp_div_less mult.commute power_Suc) 
  let ?n  = "x * (2 ^ w) ^ Suc l + y"
  let ?nd = "?n div 2^w"
  let ?nm = "?n mod 2^w" 
  have 2: "nat_to_words w ?n = (nat_to_words w ?nd)@[?nm]" 
    using nat_to_words_h assms(2,3) by auto
  have 3: "?nd = x * (2 ^ w) ^ l + ?yd"
    by (smt (z3) C.prems(1) div_mult_self3 gr_implies_not0 mult.commute mult.left_commute
        power_Suc power_eq_0_iff zero_less_Suc) 
  have 4: "?nm = ?ym"
    by (metis add.commute mod_mult_self2 mult.left_commute power_Suc) 
  have 5: "nat_to_words w ?nd = nat_to_words w x @ nat_to_words_len w ?yd l" 
    using C(1) 3 assms(2,3) 1 by presburger
  have 6: "(nat_to_words_len w ?yd l)@[?nm] = nat_to_words_len w y (Suc l)"
    using 4 assms(3) diff_Suc_1 nat_to_words_len_h2 zero_less_Suc by presburger 
  then show ?case  by (metis 2 5 6 append_assoc)  
qed

lemma sum_to_words_len:
  assumes "y < (2^w)^l"  "0 < x"  "0 < w"
  shows   "nat_to_words_len w (x*((2^w)^l) + y) (k+l) = 
          (nat_to_words_len w x k) @ (nat_to_words_len w y l)"
  using assms nat_to_words_len_def nat_to_words_len_upbnd sum_to_words by force

lemma nat_to_words_len_bnd:
  assumes "y < (2^w)^l"
  shows   "nat_to_words_len w y (k+l) = (replicate k 0) @ (nat_to_words_len w y l)"
  by (smt (z3) add_diff_cancel_right' append_assoc assms length_append length_replicate 
               nat_to_words_len_def nat_to_words_len_upbnd replicate_add)

lemma sum_to_words_len2:
  assumes "y < (2^w)^l"  "0 < w"
  shows   "nat_to_words_len w (x*((2^w)^l) + y) (k+l) = 
          (nat_to_words_len w x k) @ (nat_to_words_len w y l)"
proof (cases "x = 0")
  case T: True
  then show ?thesis
    by (simp add: assms(1) nat_to_words_len_bnd) 
next
  case False
  then have  "0 < x" by fast
  then show ?thesis using assms sum_to_words_len by blast
qed
 

section\<open>Words to Nat\<close>
text\<open>Convert any word string to a natural number.  When the words are valid (< (2^w)), this 
operation is the inverse of nat_to_words.\<close>

definition words_to_nat :: "nat \<Rightarrow> words \<Rightarrow> nat" where
  "words_to_nat w = foldl (%b a. (2^w)*b + a) 0"

lemma one_word_to_nat [simp]: "words_to_nat w [n] = n"
  by (simp add: words_to_nat_def) 
  
lemma words_to_nat_empty [simp]: "words_to_nat w [] = 0" 
  by (simp add: words_to_nat_def) 

lemma words_to_nat_cons [simp]: 
  "words_to_nat w (b # bs) = b*((2^w)^ length bs) + words_to_nat w bs"
proof - 
  let ?words_to_nat' = "foldl (\<lambda>bn b. (2^w)*bn + b)"
  have helper: "\<And>base. ?words_to_nat' base bs = base * (2^w) ^ length bs + ?words_to_nat' 0 bs"
  proof (induct bs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs base)
    show ?case
      apply (simp only: foldl_Cons)
      apply (subst Cons [of "(2^w)*base + x"])
      apply simp
      apply (subst Cons [of "x"])
      apply (simp add:add_mult_distrib)
      done
  qed
  show ?thesis by (simp add: words_to_nat_def) (rule helper)
qed

lemma words_to_nat_concat:
  "words_to_nat w (as @ bs) = (words_to_nat w as)*((2^w)^ length bs) + words_to_nat w bs"
  using words_to_nat_cons words_to_nat_def apply (induct as)
  apply (metis add.left_neutral append_Nil mult_0 words_to_nat_empty)
  by (metis (no_types, lifting) diff_zero foldl_Cons foldl_append le_add_diff_inverse 
      mult_0_right zero_le)

lemma words_to_nat_append: "words_to_nat w (as @ [a]) = (words_to_nat w as)*(2^w) + a"
  using words_to_nat_concat by force

lemma words_to_nat_cons_zero: "words_to_nat w (0#bs) = words_to_nat w bs"
  using words_to_nat_cons by auto

lemma words_to_nat_prepend_zeros: "words_to_nat w ((replicate z 0) @ bs) = words_to_nat w bs" 
  apply (induction z) 
   apply simp 
  by simp

lemma words_to_zero_intro: 
  assumes "\<forall>i<length os. os ! i = 0" 
  shows   "words_to_nat w os = 0"
using assms proof (induction os)
  case Nil
  then show ?case by simp
next
  case 1: (Cons a os)
  have 2: "a = 0"                  using 1(2) by auto
  have 3: "words_to_nat w os = 0"  using 1 by fastforce
  show ?case                       using 2 3 words_to_nat_cons by force
qed

lemma words_to_zero_dest:
  assumes "words_to_nat w os = 0"
  shows   "\<forall>i<length os. os ! i = 0"
proof -
  let ?l = "length os"
  show ?thesis using assms proof (induction ?l arbitrary: os)
    case 0
    then show ?case by auto
  next
    case 1: (Suc x)
    let ?e = "last os"
    let ?b = "butlast os"
    have 2: "os = ?b @ [?e]" by (metis 1(2) append_butlast_last_id list.size(3) nat.distinct(1))
    have 3: "words_to_nat w os = (words_to_nat w ?b)*(2^w) + ?e" by (metis 2 words_to_nat_append)
    have 4: "length ?b = x"                                      using 1(2) by simp
    have 5: "?e = 0"                                             using 3 1(3) by fastforce
    have 6: "words_to_nat w ?b = 0"                              using 3 1(3) by force
    have 7: "\<forall>i<x. ?b ! i = 0"                                   using 1(1) 4 6 by blast
    show ?case  by (metis 1(2) 2 4 5 7 less_Suc_eq nth_append nth_append_length) 
  qed
qed

lemma words_to_zero: "words_to_nat w os = 0 \<longleftrightarrow> (\<forall>i<length os. os ! i = 0)"
  using words_to_zero_intro words_to_zero_dest by blast

lemma nat_to_words_to_nat: 
  assumes "0 < w"
  shows   "words_to_nat w (nat_to_words w n) = n"
proof - 
  let ?l = "length (nat_to_words w n)"
  show ?thesis using assms proof (induction ?l arbitrary: n w)
    case 0
    then show ?case using nat_to_words_nil_iff_zero by simp
  next
    case 1: (Suc x)
    have 2: "0 < n" using 1 nat_bnd_word_len_inv by fastforce 
    let ?d = "n div (2^w)"
    let ?m = "n mod (2^w)" 
    have 3: "nat_to_words w n = (nat_to_words w ?d) @ [?m]" using 1(3) 2 nat_to_words_h by blast
    have 4: "length (nat_to_words w ?d) = x" by (simp add: 1 3 Suc_inject length_append_singleton)
    have 5: "words_to_nat w (nat_to_words w ?d) = ?d" using 1 4 by presburger
    have    "words_to_nat w (nat_to_words w n) = ?d*(2^w) + ?m" 
      using 3 5 words_to_nat_append by presburger 
    then show ?case by presburger
  qed
qed

lemma words_to_nat_to_words:
  assumes "\<forall>b\<in>set bs. b < (2^w)"  "0 < nth bs 0"  "0 < w"
  shows   "nat_to_words w (words_to_nat w bs) = bs"
proof -
  let ?l = "length bs"
  show ?thesis using assms proof (induction ?l arbitrary: bs w)
    case 0
    then have "bs = []" by auto
    then show ?case by simp
  next
    case 1: (Suc x)
    then show ?case proof (cases)
      assume 11: "Suc x = 1"
      have 12: "0 < length bs" using 1(2) 11 by force
      let ?c = "bs ! 0"
      have 13: "bs = [?c]"
        by (metis 1(2) 11 12 Cons_nth_drop_Suc One_nat_def Suc_leI drop0 drop_all)
      have 14: "?c \<in> set bs"              using 12 in_set_conv_nth by auto 
      have 15: "?c < (2^w)"               using 14 1(3) by fast 
      have 16: "words_to_nat w bs = ?c"   using 13 one_word_to_nat by metis
      have 17: "nat_to_words w ?c = [?c]" using 1(4) 15 nat_to_one_word by presburger
      show ?case using 16 17 13 by auto
    next
      assume "\<not> Suc x = 1"
      then have 20: "1 < Suc x" by auto
      have 200: "0 < length bs" using 20 1(2) by auto
      let ?c  = "last bs"
      let ?cs = "butlast bs"
      have 21: "bs = ?cs@[?c]" by (metis 1(2) append_butlast_last_id list.size(3) nat.simps(3)) 
      have 22: "words_to_nat w bs = (words_to_nat w ?cs)*(2^w) + ?c" 
                               by (metis 21 words_to_nat_append)
      have 23: "x = length ?cs"          using 1(2) 22 by auto
      have 24: "\<forall>b \<in> set ?cs. b < (2^w)" by (metis 1(3) in_set_butlastD) 
      have 25: "0 < length ?cs"          using 20 1(2) by simp
      have 26: "?cs ! 0 = bs ! 0"        using 25 nth_butlast by blast
      have 27: "words_to_nat w bs = (words_to_nat w ?cs)*(2^w) + ?c" 
                                         by (metis 21 words_to_nat_append)
      have 28: "nat_to_words w (words_to_nat w ?cs) = ?cs"  using 1(1,4,5) 23 24 26 by presburger
      have 29: "?c \<in> set bs"                                using 200 by simp
      have 30: "?c < (2^w)"                                 using 1(3) 29 by blast
      have 31: "(words_to_nat w bs) mod (2^w) = ?c"         using 27 30 by simp
      have 32: "(words_to_nat w bs) div (2^w) = (words_to_nat w ?cs)" using 27 30 by simp
      have 33: "0 < words_to_nat w bs" by (metis 1(4) 200 words_to_zero gr0I) 
      show ?case using 21 31 32 33 28 nat_to_words_h 1(5) by presburger
    qed
  qed
qed

lemma words_to_nat_len_bnd:
  assumes "\<forall>b\<in>set bs. b < (2^w)"  "0 < w" 
  shows   "words_to_nat w bs < (2^w)^(length bs)" 
using assms proof (induction bs arbitrary: w)
  case Nil
  then show ?case by fastforce
next
  case 1: (Cons a bs)
  let ?l = "length bs" 
  have 2: "\<forall>b\<in>set bs. b < (2^w)"          using 1(2) by simp
  have 3: "words_to_nat w bs < (2^w)^?l"  using 1(1,3) 2 by blast
  show ?case
    by (metis 1(2,3) 3 diff_Suc_Suc diff_diff_cancel diff_le_self length_Cons linorder_not_less 
              nat_bnd_word_len nat_lowbnd_word_len neq0_conv nth_Cons_0 words_to_nat_cons_zero 
              words_to_nat_to_words verit_comp_simplify1(1)) 
qed

lemma trunc_words_to_nat: 
  assumes "as = nat_to_words w n"  "as = bs@[b]"  "0 < w" 
  shows   "words_to_nat w bs = (n div (2^w))"
  by (metis assms Nil_is_append_conv append1_eq_conv n_div_2tow_cases nat_to_words_h 
            nat_to_words_to_nat not_Cons_self zero_to_word)

lemma high_words_to_nat:
  assumes "as = nat_to_words w n"  "as = bs@cs"  "0 < w"
  shows   "words_to_nat w bs = (n div (2^w)^(length cs))"
proof - 
  have 1: "words_to_nat w as = n" using assms(1,3) nat_to_words_to_nat by blast
  have 2: "words_to_nat w as = (words_to_nat w bs)*((2^w)^(length cs)) + words_to_nat w cs"
    using assms(2) words_to_nat_concat by simp
  have 3: "\<forall>c\<in>set cs. c < (2^w)" 
    by (metis assms(1,2) words_upper_bound append.assoc in_set_conv_decomp) 
  have 4: "words_to_nat w cs < (2^w)^(length cs)" 
    using 3 assms(3) words_to_nat_len_bnd by presburger
  have 5: "n = (words_to_nat w bs)*((2^w)^(length cs)) + words_to_nat w cs" using 1 2 by meson
  show ?thesis using 4 5 by simp
qed

lemma low_words_to_nat:
  assumes "as = nat_to_words w n"  "as = bs@cs"  "0 < w" 
  shows   "words_to_nat w cs = (n mod (2^w)^(length cs))"
  by (metis (no_types, lifting) add_left_cancel assms div_mult_mod_eq high_words_to_nat 
            nat_to_words_to_nat words_to_nat_concat)

lemma trunc_words_to_nat_len:
  assumes "as = nat_to_words_len w n l"  "as = bs@[b]"  "0 < w"
  shows   "words_to_nat w bs = (n div (2^w))"
proof (cases "n=0")
  case T: True
  then show ?thesis proof (cases "l=0")
    case True
    then show ?thesis
      using assms nat_to_words_len_def trunc_words_to_nat by force 
  next
    case F0: False
    then have F1: "0 < l"          by blast
    have F2: "as = replicate l 0"  using assms(1) T zero_to_words_len by presburger
    have F3: "b = 0"               by (metis F0 F2 assms(2) last_replicate last_snoc) 
    have F4: "bs = replicate (l-1) 0"
      by (metis Cons_replicate_eq F1 F2 F3 append_eq_append_conv assms(2) replicate_append_same) 
    have F5: "n div (2^w) = 0"     by (simp add: T) 
    show ?thesis  by (metis F4 F5 append_Nil2 words_to_nat_empty words_to_nat_prepend_zeros) 
  qed
next
  case False
  then show ?thesis
    using assms nat_to_words_h nat_to_words_len_def trunc_words_to_nat words_to_nat_prepend_zeros 
    by auto 
qed

lemma low_words_to_nat2:
  assumes "as = nat_to_words_len w n l"  "as = bs@cs"  "0 < w" 
  shows   "words_to_nat w cs = (n mod (2^w)^(length cs))"
proof (cases "n=0")
case T: True
  then show ?thesis proof (cases "l=0")
    case True
    then show ?thesis using T assms(1,2) by force 
  next
    case False
    then show ?thesis
      by (metis T assms(1,2,3) bits_mod_0 length_0_conv nat_to_words_len_def 
                nat_to_words_nil_iff_zero2 word_length_def words_to_nat_concat words_to_nat_empty 
                words_to_nat_prepend_zeros zero_eq_add_iff_both_eq_0) 
  qed
next
  case F: False
  let ?xs = "nat_to_words w n" 
  let ?xl = "length ?xs"
  let ?zl = "l - ?xl"
  let ?zs = "replicate ?zl 0"
  have 1: "as = ?zs @ ?xs"         using assms(1) nat_to_words_len_def by meson
  have 2: "bs @ cs = ?zs @ ?xs"    using 1 assms(2) by argo
  let ?cl = "length cs"
  let ?bl = "length bs" 
  have 3: "?bl + ?cl = ?zl + ?xl"  by (metis 2 length_append length_replicate) 
  then show ?thesis proof (cases "?zl = 0")
    case True
    then show ?thesis              using 1 assms(2,3) low_words_to_nat by force 
  next
     case False
     then show ?thesis proof (cases "length cs \<le> ?xl")
       case T1: True
       let ?ds = "take (?xl - ?cl) ?xs"
       have "?xs = ?ds @ cs" 
         by (smt (verit, ccfv_threshold) 1 assms(2) T1 append_assoc append_eq_append_conv 
                 append_take_drop_id diff_diff_cancel length_drop) 
       then show ?thesis            using assms(3) low_words_to_nat by blast 
     next
       case F1: False
       have F2: "?xl < ?cl"         using F1 by linarith
       have F3: "?bl < ?zl"         using F2 3 by force 
       have F4: "cs = drop ?bl as"  using assms(2) by force
       let ?ds = "replicate (?cl - ?xl) 0" 
       have "cs = ?ds @ ?xs"        using 2 F3 F4 assms(2) by force 
       then show ?thesis
         by (metis Euclidean_Rings.mod_less F1 assms(3) less_or_eq_imp_le nat_lowbnd_word_len
              nat_to_words_to_nat not_less words_to_nat_prepend_zeros)
    qed
  qed
qed

lemma words_to_nat_to_strip_words:
  assumes "\<forall>b\<in>set bs. b < (2^w)" 
  shows   "nat_to_words w (words_to_nat w bs) = words_strip_zero bs" 
proof (cases "w = 0")
  case T: True
  have T1: "\<forall>b\<in>set bs. b < 1"      using T assms(1) by fastforce
  have T2: "\<forall>b\<in>set bs. b = 0"      using T1 by fastforce
  let ?bl = "length bs"
  have T3: "bs = replicate ?bl 0"  by (simp add: T2 replicate_length_same) 
  show ?thesis
    by (metis (no_types) T T3 append_Nil2 nat_to_zero_bit_words strip_prepend_zeros 
        words_strip_zero.simps(1)) 
next
  case F: False
  let ?bl = "length bs"
  let ?s =  "words_strip_zero bs"
  let ?sl = "length ?s"
  let ?z =  "(replicate (?bl-?sl) 0)"
  let ?zl = "length ?z" 
  have 1: "bs = ?z @ ?s"                          using strip_zero_concat by blast
  have 2: "words_to_nat w bs = words_to_nat w ?s" using 1 words_to_nat_prepend_zeros by metis
  have 3: "\<forall>b\<in>set ?s. b\<in>set bs"                   by (metis 1 append_assoc in_set_conv_decomp) 
  have 4: "\<forall>b\<in>set ?s. b<(2^w)"                    using assms(1) 3 by blast
  show ?thesis proof (cases)
    assume 50: "?s = []"
    then show ?thesis      using 2 zero_to_word words_to_nat_empty by auto
  next
    assume 60:"?s \<noteq> []"
    have 61: "0 < ?s ! 0"  using 60 strip_zero_head by fastforce 
    have 62: "nat_to_words w (words_to_nat w ?s) = ?s" 
      using 61 4 F words_to_nat_to_words by blast
    show ?thesis           using 2 62 by simp
  qed
qed

lemma nat_to_words_len_to_nat: 
  assumes "0 < w"
  shows   "words_to_nat w (nat_to_words_len w x xLen) = x"
  using assms nat_to_words_len_def nat_to_words_to_nat words_to_nat_prepend_zeros by presburger

lemma words_to_nat_to_words_len:
  assumes "l = length os"  "\<forall>b\<in>set os. b < (2^w)"  
  shows   "nat_to_words_len w (words_to_nat w os) l = os"
  using assms strip_zero_concat words_to_nat_to_strip_words nat_to_words_len_def by presburger

lemma words_to_nat_to_words_len2:
  assumes "l = length os"  "words_valid w os"  
  shows   "nat_to_words_len w (words_to_nat w os) l = os"
  using assms words_valid_def words_to_nat_to_words_len by auto

lemma words_strip0_to_nat_len_bnd:
  assumes "\<forall>b\<in>set bs. b < (2^w)" 
  shows   "words_to_nat w bs < (2^w)^(length (words_strip_zero bs))"
proof (cases "w = 0")
  case T: True
  have T1: "\<forall>b\<in>set bs. b < 1"      using T assms(1) by fastforce
  have T2: "\<forall>b\<in>set bs. b = 0"      using T1 by fastforce
  let ?bl = "length bs"
  have T3: "bs = replicate ?bl 0"  by (simp add: T2 replicate_length_same) 
  then show ?thesis
    by (metis One_nat_def T less_Suc0 nth_replicate power_0 power_one words_to_zero) 
next
  case False
  then show ?thesis 
    by (simp add: assms word_length_def word_length_eq2 words_to_nat_to_strip_words)
qed

lemma words_strip0_to_nat_len_bnd2:
  assumes "\<forall>b\<in>set bs. b < (2^w)"  "length (words_strip_zero bs) \<le> x" 
  shows   "words_to_nat w bs < (2^w)^x"
  by (meson assms leD leI le_less_trans nat_power_less_imp_less words_strip0_to_nat_len_bnd 
            zero_less_numeral zero_less_power)

lemma word_len_comp:
  assumes "word_length w a < word_length w b"
  shows   "a < b"
  by (metis assms less_le_trans nat_bnd_word_len_inv2 word_length_eq2 le0 le_less 
            nat_to_zero_bit_word_len)

lemma word_len_shift:
  assumes "word_length w X = l"  "0 < X"  "0 < w" 
  shows   "word_length w (X*((2^w)^n)) = l + n"
proof - 
  have  0: "0 < l"           using assms nat_to_words_nil_iff_zero2 neq0_conv by blast 
  have l1: "(2^w)^(l-1) \<le> X" using assms word_length_eq by blast 
  have l2: "(2^w)^(l-1)*(2^w)^n \<le> X*(2^w)^n" using l1 by force 
  have l3: "(2^w)^(l-1+n) \<le> X*(2^w)^n"       by (metis l2 power_add) 
  have l4: "(2^w)^(l+n-1) \<le> X*(2^w)^n"       using l3 0 by force
  have u1: "X < (2^w)^l"                     by (simp add: assms(1,3) word_length_eq2)
  have u2: "X*(2^w)^n < (2^w)^(n+l)"         by (simp add: u1 power_add)
  show ?thesis
    by (metis assms(2,3) l4 u2 add.commute mult_pos_pos word_length_eq zero_less_numeral 
        zero_less_power) 
qed

lemma word_len_le_shift:
  assumes "word_length w X \<le> l"  "0 < w"  
  shows   "word_length w (X*((2^w)^n)) \<le> l + n"
  by (metis add_le_mono1 assms mult_is_0 neq0_conv trans_le_add1 word_len_shift)

lemma word_len_shift_add:
  assumes "word_length w X = l"  "0 < X"  "a < (2^w)^n"  "0 < w"
  shows   "word_length w (X*((2^w)^n) + a) = l + n"
proof - 
  have 1: "X*((2^w)^n) + a = X*((2^w)^n) OR a" 
    by (metis assms(3) OR_sum_nat_hilo_2 mult.commute power_mult)
  have 2: "word_length w (X*((2^w)^n)) = l + n"  using assms(1,2,4) word_len_shift by presburger
  have 3: "X*((2^w)^n) < (2^w)^(l+n)"            by (simp add: 2 assms(4) word_length_eq2) 
  have 4: "a < (2^w)^(n+l)" 
    by (metis assms(3,4) less_le_trans add.right_neutral add_less_cancel_left less_nat_zero_code 
        nat_bnd_word_len2 nat_lowbnd_word_len2 not_le) 
  have 5: "X*((2^w)^n) OR a < (2^w)^(n+l)"  by (metis 3 4 add.commute nat_OR_upper power_mult)
  have 6: "(2^w)^(l+n-1) \<le> X*((2^w)^n)"
    by (metis 2 assms(2,4) word_length_eq nat_0_less_mult_iff zero_less_numeral zero_less_power)
  have 7: "(2^w)^(l+n-1) \<le> X*((2^w)^n) + a" using 6 by linarith
  have 8: "X*((2^w)^n) + a < (2^w)^(l+n)"   by (metis 1 5 add.commute)
  have 9: "0 < X*((2^w)^n) + a"             using assms(2) by simp
  show ?thesis   using 7 8 9 assms(4) word_length_eq add.commute by presburger
qed

lemma word_len_mult1:
  assumes "word_length w A = l"  "word_length w B = k"  "0 < A" 
  shows   "word_length w (A*B) \<le> l + k"
  by (smt (verit, ccfv_SIG) assms less_or_eq_imp_le mult_less_cancel1 nat_to_zero_bit_word_len 
     neq0_conv not_less_iff_gr_or_eq word_len_comp word_len_shift word_length_eq2)

lemma word_len_mult2:
  assumes "word_length w A = l"  "word_length w B = k"  "0 < A"  "0 < B"  "0 < w"
  shows   "l + k - 1 \<le> word_length w (A*B)"
proof - 
  have A: "(2^w)^(l-1) \<le> A" using assms(1,3,5) word_length_eq by blast 
  have B: "(2^w)^(k-1) \<le> B" using assms(2,4,5) word_length_eq by blast
  have k: "0 < k"           using assms(2,4,5) nat_to_words_nil_iff_zero2 neq0_conv by blast 
  have 1: "(2^w)^(l - 1 + k - 1) \<le> A*B" 
    by (metis A B k power_add Nat.add_diff_assoc2 One_nat_def Suc_leI add.commute mult_le_mono)
  show ?thesis 
    by (metis 1 A k Nat.add_diff_assoc2 One_nat_def Suc_leI Suc_pred add_gr_0 assms(1,5) 
        diff_is_0_eq' nat_le_linear nat_lowbnd_word_len2) 
qed

text \<open>These conversions between natural numbers and words are injections. Mostly.\<close>

lemma nat_to_words_inj:
  assumes "nat_to_words w n = nat_to_words w m"  "0 < w" 
  shows   "n = m" 
  by (metis assms nat_to_words_to_nat)

lemma nat_to_words_len_inj:
  assumes "nat_to_words_len w n l = nat_to_words_len w m l"  "0 < w" 
  shows   "n = m" 
  by (metis assms nat_to_words_len_to_nat)

lemma words_to_nat_inj:
  assumes "words_to_nat w as = words_to_nat w bs"  "0 < w"  "0 < hd as"  "0 < hd bs" 
          "words_valid w as" "words_valid w bs" 
  shows   "as = bs" 
  by (metis assms words_to_nat_to_words words_valid_def hd_conv_nth words_strip_zero.simps(1) 
            words_to_nat_to_strip_words) 

lemma words_to_nat_inj':
  assumes "words_to_nat w as = words_to_nat w bs"  "words_valid w as"  "words_valid w bs" 
  shows   "words_strip_zero as = words_strip_zero bs"
  by (metis assms nat_to_words_len_def strip_prepend_zeros words_to_nat_to_words_len2) 

section\<open>XOR of Words\<close>
text \<open>In the schemes contained in the PKCS #1 standard, word strings are formed by converting from
integers and/or concatenating other word strings.  Then word strings of the same length may be
XORed together.  Here we define the XOR of words and prove the fundamental property that we will
need in PKCS #1, which is that if A XOR B = C, then B XOR C = A. Note that we could define 
xor_words so that it pads the shorter input with zeroes so that the output is the length of the 
longer input.  Since the PKCS1 standard only XORs words of the same length, this is not something
that we concern ourselves with here.\<close>

definition xor_words :: "words \<Rightarrow> words \<Rightarrow> words" where
  "xor_words xs ys = map2 (XOR) xs ys"

lemma xor_words_length: 
  assumes "length a \<le> length b"
  shows   "length (xor_words a b) = length a"
  using assms xor_words_def by simp  

lemma xor_words_length2: "length (xor_words a b) = min (length a) (length b)" 
  using xor_words_def by auto

lemma xor_valid_words:
  assumes "words_valid w xs"  "words_valid w ys" 
  shows   "words_valid w (xor_words xs ys)"
proof - 
  {
  fix i
  assume 0: "i < length (xor_words xs ys)"
  have 1: "(xor_words xs ys) ! i = (xs ! i) XOR (ys ! i)" using 0 xor_words_def by simp
  have 2: "i < length xs"  using 0 xor_words_length2 by auto
  have 3: "i < length ys"  using 0 xor_words_length2 by auto
  have 4: "xs ! i < (2^w)" using 2 assms(1) words_valid_def by force
  have 5: "ys ! i < (2^w)" using 3 assms(2) words_valid_def by force
  have 6: "(xs ! i) XOR (ys ! i) < (2^w)"  using 4 5 nat_XOR_upper by blast 
  have 7: "(xor_words xs ys) ! i < (2^w)"  using 1 6 by auto
  }
  then show ?thesis by (metis in_set_conv_nth words_valid_def) 
qed

lemma xor_words_symm: "xor_words xs ys = xor_words ys xs" 
  using case_prod_unfold map2_map_map map_eq_conv zip_commute zip_map_fst_snd
        Bit_Operations.semiring_bit_operations_class.xor.commute xor_words_def
  by (smt (z3))

lemma xor_words_cons: "xor_words (a#as) (b#bs) = (a XOR b)#(xor_words as bs)"
  using xor_words_def by auto

lemma xor_words_append: 
  assumes "length as = length bs"
  shows "xor_words (as@[a]) (bs@[b]) = (xor_words as bs)@[a XOR b]"
  using assms xor_words_def by simp

lemma nat_xor_inv:
  assumes "(a::nat) XOR b = c"
  shows   "b XOR c = a"
  by (metis assms bit.xor_self xor.left_commute xor.right_neutral xor_nat_def)

text\<open>This is the main fact about the XOR of word strings that we will need to show that encoding
and then decoding a message (for example in section 7 of PKCS #1) will get back to where 
you started.\<close>
lemma words_xor_inv:
  assumes "xor_words as bs = cs"  "length as = length bs"  "length as = n"
  shows   "xor_words bs cs = as"
  using assms xor_words_def apply (induction n arbitrary: as bs cs)
   apply auto
  by (smt (z3) Nil_is_map_conv hd_Cons_tl hd_zip length_Suc_conv length_map list.map(2) 
      list.map_sel(1) list.sel(3) map_fst_zip map_snd_zip nat_xor_inv split_conv zip_map_fst_snd) 

lemma words_xor_inv2:
  assumes "length as = length bs"
  shows   "xor_words (xor_words as bs) bs = as"
  using assms words_xor_inv xor_words_symm by presburger


section \<open>Abbreviations\<close>

type_synonym octets = words
type_synonym bits   = words

abbreviation bit_length :: "nat \<Rightarrow> nat" where
  "bit_length n \<equiv> word_length 1 n" 

abbreviation nat_to_bits :: "nat \<Rightarrow> words" where
  "nat_to_bits n \<equiv> nat_to_words 1 n"

abbreviation nat_to_bits_len :: "nat \<Rightarrow> nat \<Rightarrow> words" where
  "nat_to_bits_len n l \<equiv> nat_to_words_len 1 n l"

abbreviation bits_to_nat :: "words \<Rightarrow> nat" where
  "bits_to_nat n \<equiv> words_to_nat 1 n" 

abbreviation bits_valid :: "words \<Rightarrow> bool" where
  "bits_valid bs \<equiv> words_valid 1 bs" 

lemma bitLenLog2Pow2:
  assumes "n = 2^m"
  shows   "bit_length n = \<lceil>log 2 n\<rceil> + 1"
proof - 
  let ?b = "bit_length n"
  let ?l = "\<lceil>log 2 (real n)\<rceil>"
  have l1: "log 2 (real n) = m"  using assms by simp
  have l2: "?l = m"              using l1 by auto
  have b1: "?b = m + 1"          by (simp add: assms word_length_eq) 
  show ?thesis                   using l2 b1 by simp
qed

lemma bitLenLog2NotPow2: 
  assumes "0 < n"  "b = bit_length n"  "2^(b-1) < n"
  shows   "b = \<lceil>log 2 n\<rceil>"
  by (smt (z3) One_nat_def Suc_pred add.commute assms(1,2,3) ceiling_log_nat_eq_if 
      less_or_eq_imp_le nat_to_words_nil_iff_zero2 neq0_conv of_nat_1 of_nat_add one_add_one 
      plus_1_eq_Suc power_one_right word_length_eq2)

lemma bitLenLog2Odd:
  assumes "odd p"  "1 < p" 
  shows   "bit_length p = \<lceil>log 2 p\<rceil>"
  using assms(1,2) wordLenLog2Odd by force

lemma bitLenLog2Prime:
  assumes "2 < p"  "prime p"
  shows   "bit_length p = \<lceil>log 2 p\<rceil>"
  using assms(1,2) bitLenLog2Odd prime_gt_1_nat prime_odd_nat by blast

text \<open>I use this fact in many places, so it's convenient to give it a name.\<close>
lemma Twoto8 [simp]: "(2::nat)^8 = 256" 
  by simp

abbreviation octet_length :: "nat \<Rightarrow> nat" where
  "octet_length n \<equiv> word_length 8 n" 

abbreviation nat_to_octets :: "nat \<Rightarrow> words" where
  "nat_to_octets n \<equiv> nat_to_words 8 n"

abbreviation nat_to_octets_len :: "nat \<Rightarrow> nat \<Rightarrow> words" where
  "nat_to_octets_len n l \<equiv> nat_to_words_len 8 n l"

abbreviation octets_to_nat :: "words \<Rightarrow> nat" where
  "octets_to_nat n \<equiv> words_to_nat 8 n" 

abbreviation octets_valid :: "words \<Rightarrow> bool" where
  "octets_valid bs \<equiv> words_valid 8 bs" 

abbreviation xor_octets :: "words \<Rightarrow> words \<Rightarrow> words" where
  "xor_octets \<equiv> xor_words"

lemma octetLenLog2Odd:
  assumes "odd p"  "1 < p" 
  shows   "octet_length p = \<lceil>(log 2 p)/8\<rceil>"
  using assms(1,2) wordLenLog2Odd by auto 

lemma octetLenLog2Prime:
  assumes "prime p"  "2 < p" 
  shows   "octet_length p = \<lceil>(log 2 p)/8\<rceil>"
  by (simp add: assms(1,2) wordLenLog2Prime)

abbreviation word32_length :: "nat \<Rightarrow> nat" where
  "word32_length n \<equiv> word_length 32 n"

abbreviation nat_to_word32s :: "nat \<Rightarrow> words" where
  "nat_to_word32s n \<equiv> nat_to_words 32 n"

abbreviation word32s_to_nat :: "words \<Rightarrow> nat" where
  "word32s_to_nat n \<equiv> words_to_nat 32 n" 

abbreviation word32s_valid :: "words \<Rightarrow> bool" where
  "word32s_valid bs \<equiv> words_valid 32 bs" 

abbreviation word64_length :: "nat \<Rightarrow> nat" where
  "word64_length n \<equiv> word_length 64 n"

abbreviation nat_to_64words :: "nat \<Rightarrow> words" where
  "nat_to_64words n \<equiv> nat_to_words 64 n"

abbreviation word64s_to_nat :: "words \<Rightarrow> nat" where
  "word64s_to_nat n \<equiv> words_to_nat 64 n" 

abbreviation word64s_valid :: "words \<Rightarrow> bool" where
  "word64s_valid bs \<equiv> words_valid 64 bs" 

text\<open>Some short-hands for converting between octets and bits.\<close>
definition octets_to_bits :: "octets \<Rightarrow> bits" where
  "octets_to_bits os = nat_to_bits (octets_to_nat os)"

definition octets_to_bits_len :: "octets \<Rightarrow> bits" where
  "octets_to_bits_len os = 
  ( let l = 8*(length os) in
      nat_to_bits_len (octets_to_nat os) l
  )" 

definition bits_to_octets :: "bits \<Rightarrow> octets" where
  "bits_to_octets bs = nat_to_octets (bits_to_nat bs)"

definition bits_to_octets_len :: "bits \<Rightarrow> octets" where
  "bits_to_octets_len bs = 
  ( let l = length bs;
        x = (if l mod 8 = 0 then (l div 8) else (l div 8 + 1)) in
      nat_to_octets_len (bits_to_nat bs) x  
  )" 

lemma octets_to_bits_to_nat: 
  "(bits_to_nat (octets_to_bits os)) = (octets_to_nat os)"
  by (simp add: nat_to_words_to_nat octets_to_bits_def)

lemma octets_to_bits_len_to_nat: 
  "(bits_to_nat (octets_to_bits_len os)) = (octets_to_nat os)"
  by (simp add: nat_to_words_len_to_nat octets_to_bits_len_def)

lemma bits_to_octets_to_nat: 
  "(octets_to_nat (bits_to_octets bs)) = (bits_to_nat bs)"
  by (simp add: nat_to_words_to_nat bits_to_octets_def)

lemma bits_to_octets_len_to_nat: 
  "(octets_to_nat (bits_to_octets_len bs)) = (bits_to_nat bs)"
  by (metis bits_to_octets_len_def nat_to_words_len_to_nat zero_less_numeral)

lemma octets_to_bits_len_len: 
  assumes "octets_valid os" 
  shows   "length (octets_to_bits_len os) = 8 * length os"
  by (smt (verit, ccfv_SIG) assms nat_to_words_len_upbnd octets_to_bits_len_def power_mult 
          power_one_right words_to_nat_len_bnd words_valid_def zero_less_numeral)

lemma bits_to_octets_len_len:
  assumes "bits_valid bs"  "l = length bs" 
          "x = (if l mod 8 = 0 then (l div 8) else (l div 8 + 1))"
  shows   "length (bits_to_octets_len bs) = x"
proof - 
  let ?n = "bits_to_nat bs"
  have 1: "?n < 2^l" 
    by (metis assms(1,2) words_to_nat_len_bnd words_valid_def power_one_right zero_less_one) 
  let ?m = "l mod 8"
  let ?d = "l div 8"
  have 2: "l = ?d*8 + ?m"  using mod_div_decomp by presburger
  have 3: "?m < 8"         by (meson mod_less_divisor zero_less_numeral)
  show ?thesis proof (cases "?m = 0")
    case True
    then show ?thesis
      by (smt (z3) 1 2 Nat.add_0_right assms(2,3) bits_to_octets_len_def mult.commute 
              nat_to_words_len_upbnd power_mult) 
  next
    case F0: False
    have F1: "x = ?d + 1" using F0 assms(3) by presburger
    have F2: "l < 8*x"    using F1 2 3 by linarith
    have F3: "?n < (2^8)^x" 
      by (metis (no_types, lifting) 1 F2 power_mult le_less_trans less_imp_le_nat 
                one_less_numeral_iff power_strict_increasing_iff semiring_norm(76)) 
    show ?thesis 
      using F0 F1 F3 nat_to_words_len_upbnd assms(2) bits_to_octets_len_def by auto 
  qed
qed

lemma octets_valid_to_bits_valid:
  assumes "octets_valid os"
  shows   "bits_valid (octets_to_bits os)"
  using nat_to_words_valid octets_to_bits_def by presburger

lemma octets_valid_to_bits_len_valid:
  assumes "octets_valid os"
  shows   "bits_valid (octets_to_bits_len os)"
  using nat_to_words_len_valid octets_to_bits_len_def by auto

lemma bits_valid_to_octets_valid:
  assumes "bits_valid bs"
  shows   "octets_valid (bits_to_octets bs)"
  using bits_to_octets_def nat_to_words_valid by presburger 

lemma bits_valid_to_octets_len_valid:
  assumes "bits_valid bs"
  shows   "octets_valid (bits_to_octets_len bs)"
  by (metis bits_to_octets_len_def nat_to_words_len_valid)


section \<open>Bit-Level Operations\<close>
text\<open>While most of the PKCS #1 standard only deals with octet-level (byte-level) operations, the
signature scheme does some bit-level manipulations.  We include the appropriate definitions and
lemmas for those here.\<close>

subsection \<open>Set/Test High Bits\<close>

definition numBits_to_numOctets :: "nat \<Rightarrow> nat" where
  "numBits_to_numOctets numBits = (if (numBits mod 8 = 0) then (numBits div 8) 
                                                          else (numBits div 8 + 1))"
lemma emLen_emBits:
  assumes "emLen = numBits_to_numOctets emBits"
  shows   "(8*emLen - emBits < 8) \<and> (0 \<le> 8*emLen - emBits)"
proof (cases "emBits mod 8 = 0")
  case True
  then have "emLen = emBits div 8" using assms(1) numBits_to_numOctets_def by presburger
  then have "8*emLen = emBits"     using True by fastforce 
  then show ?thesis                by simp
next
  case 1: False
  let ?m = "emBits mod 8"
  let ?d = "emBits div 8" 
  have 2: "?m < 8 \<and> 0 < ?m"    using 1 by fastforce 
  have 3: "emBits = ?d*8 + ?m" by presburger
  have 4: "emLen = ?d + 1"     using 1 assms(1) numBits_to_numOctets_def by presburger
  have 5: "8*emLen - emBits = (8*?d + 8) - (8*?d + ?m)" using 3 4 by fastforce
  have 6: "8*emLen - emBits = 8 - ?m"                   using 5 by linarith
  show ?thesis  using 2 6 by simp
qed

definition SetLeftmostBits :: "nat \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> octets" where
  "SetLeftmostBits emLen emBits OctetsIn = 
  ( if  OctetsIn = [] then [] else
  ( let x                = 8*emLen - emBits;
        leftmostOctetIn  = hd OctetsIn;
        leftmostOctetOut = leftmostOctetIn mod 2^(8-x)
    in  leftmostOctetOut # (tl OctetsIn) ))" 

definition TestLeftmostBits:: "nat \<Rightarrow> nat \<Rightarrow> octets \<Rightarrow> bool" where
  "TestLeftmostBits emLen emBits OctetsIn = 
  ( if  OctetsIn = [] then True else
  ( let leftmostOctet = hd OctetsIn;
        x             = 8*emLen - emBits
     in leftmostOctet < 2^(8-x) ))"

lemma SetLeftmostBits_valid:
  assumes "octets_valid X"
  shows   "octets_valid (SetLeftmostBits a b X)"
using assms proof (induction X)
case Nil
  then show ?case using words_valid_nil SetLeftmostBits_def by force
next
  case (Cons a X)
  have 1: "octets_valid X" by (metis list.sel(3) Cons(2) words_valid_tl) 
  show ?case
    by (metis 1 Cons.prems SetLeftmostBits_def less_imp_diff_less list.sel(3) modulo_nat_def 
        words_valid_cons words_valid_hd) 
qed

lemma SetLeftmostBits_idem:
  assumes "Y = SetLeftmostBits a b X" 
  shows   "SetLeftmostBits a b Y = Y"
  using SetLeftmostBits_def assms by force

lemma SetTestLeftmostBits:
  assumes "TestLeftmostBits a b Y"
  shows   "SetLeftmostBits  a b Y = Y"
proof (cases "Y = []")
  case True
  then show ?thesis by (simp add: SetLeftmostBits_def) 
next
  case 1: False
  let ?h = "hd Y"
  let ?t = "tl Y"
  have 2: "Y = ?h # ?t"      using 1 by simp
  let ?y = "8 - (8*a - b)"
  have 3: "?h < 2^?y"        using assms 1 TestLeftmostBits_def by metis
  have 4: "?h mod 2^?y = ?h" using 3 by fastforce
  show ?thesis               using 2 4 SetLeftmostBits_def by presburger 
qed

lemma SetLeftmostBits_len:
  "length (SetLeftmostBits a b X) = length X"
  by (simp add: SetLeftmostBits_def)

lemma SetLeftmostBits_hd: 
  assumes "X \<noteq> []"
  shows   "hd (SetLeftmostBits a b X) < 2^(8-(8*a - b))"
  using SetLeftmostBits_def assms by force

lemma SetLeftmostBits_tl: "tl (SetLeftmostBits a b X) = tl X"
  using SetLeftmostBits_def by force

lemma SetLeftmostBits_xor:
  assumes "length X = length Y" 
  shows   "SetLeftmostBits a b (xor_words X Y) =
             xor_words (SetLeftmostBits a b X) 
                        (SetLeftmostBits a b Y)"
proof - 
  let ?l = "length X"
  have "?l = length Y" using assms by blast
  then show ?thesis proof (induct ?l)
case 0
  then show ?case
    using SetLeftmostBits_def xor_words_def by auto 
next
  case 1: (Suc x)
  let ?Xh = "hd X"
  let ?Xt = "tl X"
  let ?Yh = "hd Y"
  let ?Yt = "tl Y"
  have x1: "X = ?Xh # ?Xt" by (metis 1(2)   hd_Cons_tl list.size(3) nat.simps(3)) 
  have y1: "Y = ?Yh # ?Yt" by (metis 1(2,3) hd_Cons_tl list.size(3) nat.simps(3))
  let ?c = "8 - (8*a - b)"
  let ?sX = "SetLeftmostBits a b X"
  have x2: "tl ?sX = tl X" by (metis SetLeftmostBits_tl) 
  have x3: "hd ?sX = (hd X) mod 2^?c"
    by (metis (no_types) SetLeftmostBits_def list.sel(1) list.simps(3) x1) 
  let ?sY = "SetLeftmostBits a b Y"
  have y2: "tl ?sY = tl Y" by (metis SetLeftmostBits_tl) 
  have y3: "hd ?sY = (hd Y) mod 2^?c"
    by (metis (no_types) SetLeftmostBits_def list.sel(1) list.simps(3) y1) 
  let  ?XxorY = "xor_words X Y"
  let ?sXxorY = "SetLeftmostBits a b (xor_words X Y)" 
  have xy1: "tl ?XxorY = tl ?sXxorY"
    using SetLeftmostBits_def SetLeftmostBits_tl by presburger
  have xy2: "tl ?XxorY = xor_words (tl X) (tl Y)"
    by (metis list.sel(3) x1 xor_words_cons y1)
  have xy3: "tl ?sXxorY = xor_words (tl ?sX) (tl ?sY)" using xy1 xy2 x2 y2 by argo
  have xy4: "hd ?sXxorY = (?Xh XOR ?Yh) mod (2^?c)"
    by (smt (z3) SetLeftmostBits_def list.sel(1) list.simps(3) x1 
        xor_words_cons y1)
  have xy5: "(?Xh XOR ?Yh) mod (2^?c) = (?Xh mod (2^?c)) XOR (?Yh mod (2^?c))"
    by (metis take_bit_nat_def take_bit_xor)
  have xy6: "hd ?sXxorY = (hd ?sX) XOR (hd ?sY)" using xy4 xy5 x3 y3 by presburger
  show ?case 
    using SetLeftmostBits_def xor_words_def xy2 xy3 xy6 zip_eq_Nil_iff by fastforce
  qed
qed

subsection \<open>Bit Length\<close>
text \<open>Some of these lemmas are vestigial from the previous Octets.thy.  Now they follow directly
from lemmas proved above.  But it's still nice to have them for the shorthand.\<close>

lemma bit_len: "n < 2^(bit_length n)"
  by (metis less_numeral_extra(1) power_one_right word_length_eq2) 

lemma bit_len_zero: "bit_length 0 = 0"
  by (simp add: nat_to_words_nil_iff_zero2)

lemma zero_bit_len: 
  assumes "bit_length n = 0"
  shows   "n = 0"
  by (metis assms bit_len less_one power_0) 

lemma bit_len_zero_eq: "(bit_length n = 0) = (n = 0)"
  using bit_len_zero zero_bit_len by blast

lemma less_bit_len:
  assumes "x < bit_length n"
  shows   "2^x \<le> n"
  by (metis (no_types) assms nat_bnd_word_len_inv2 power_one_right)

lemma less_bit_len2:
  assumes "n < 2^x"
  shows   "bit_length n \<le> x"
  by (meson assms less_bit_len not_less)

lemma bit_len_exact1:
  assumes "0 < bit_length n"  "bit_length n = l"
  shows   "(n < (2^l)) \<and> ((2^(l-1)) \<le> n)"
  using assms bit_len less_bit_len by force

lemma bit_len_exact2:
  assumes "0 < bit_length n"  "n < 2^l"  "2^(l-1) \<le> n"
  shows   "bit_length n = l"
  by (metis assms bit_len_zero power_one_right word_len_comp word_length_eq zero_less_one)
  
lemma bit_len_exact:  
  assumes "0 < bit_length n"
  shows   "(bit_length n = l) = ((n < (2^l)) \<and> ((2^(l-1)) \<le> n))"
  by (meson assms bit_len_exact1 bit_len_exact2)

lemma bit_len_exact3:
  assumes "0 < n"
  shows   "(bit_length n = l) = ((n < (2^l)) \<and> ((2^(l-1)) \<le> n))"
  by (metis assms bit_len_exact bit_len_zero_eq neq0_conv)

lemma bit_len_lowbnd:
  assumes "2^l \<le> n"
  shows   "l+1 \<le> bit_length n"
  by (metis Suc_eq_plus1 Suc_leI assms less_numeral_extra(1) nat_lowbnd_word_len2 power_one_right)

lemma bitLen2octLen1: 
  assumes "0 < n"  "bl = bit_length n"  "ol = octet_length n"
  shows   "numBits_to_numOctets bl = ol"
proof - 
  have 2: "(2::nat)^8 = 256" by auto
  have bl: "2^(bl-1) \<le> n \<and> n < 2^bl"
    using assms(1,2) bit_len_exact3 by blast 
  show ?thesis proof (cases "bl mod 8 = 0")
    case T0: True
    let ?x = "bl div 8"
    have T1: "8*?x = bl"                    using T0 by force
    have T2: "?x = numBits_to_numOctets bl" using T0 numBits_to_numOctets_def by presburger 
    have T3: "(2::nat)^bl = (2^8)^?x"       by (metis T1 power_mult) 
    have T4: "(2::nat)^bl = 256^?x"         using T3 by force
    have T5: "n < 256^?x"                   using T4 bl by presburger
    have T6: "(256::nat)^(?x - 1) = 2^(8*(?x - 1))"     by (simp add: power_mult) 
    have T7: "8*(?x - 1) = bl - 8"          by (simp add: T1 right_diff_distrib')
    have T8: "2^(bl - 8) \<le> n"
      by (metis assms(1,2) diff_less less_bit_len n_div_2tow_cases zero_bit_len zero_less_numeral)
    have T9: "(256::nat)^(?x - 1) \<le> n"      using T6 T7 T8 by presburger
    show ?thesis   by (metis 2 T2 T5 T9 assms(1,3) word_length_eq zero_less_numeral)
  next
    case F0: False
    let ?x = "bl div 8 + 1"
    have F1: "?x = numBits_to_numOctets bl"       using F0 numBits_to_numOctets_def by presburger
    let ?d = "bl div 8" 
    let ?m = "bl mod 8"
    have F2: "0 < ?m \<and> ?m < 8"                    using F0 by force
    have F3: "bl = 8*?d + ?m"                     by presburger
    have F4: "8*?x = 8*?d + 8"                    by simp
    have F5: "8*?x > bl"                          using F2 F3 F4 by linarith
    have F6: "(256::nat)^?x = 2^(8*?x)"           by (metis 2 power_mult)
    have F7: "(2::nat)^(8*?x) > 2^bl"             using F5 by simp
    have F8: "(256::nat)^?x > n"                  using F6 F7 bl by linarith
    have F10: "(256::nat)^(?x-1) = 2^(8*?x - 8)"  by (simp add: power_mult) 
    have F11: "8*?x - 8 = 8*?d"                   using F4 by force
    have F12: "8*?x - 8 < bl"                     using F11 F3 F2 by presburger
    have F13: "(256::nat)^(?x-1) \<le> n"             by (metis F10 F12 assms(2) less_bit_len) 
    show ?thesis  by (metis 2 F1 F8 F13 assms(1,3) word_length_eq zero_less_numeral) 
  qed
qed

lemma bitLen2octLen2: 
  assumes "0 < n"  "bl = bit_length n"  "numBits_to_numOctets bl = ol"
  shows   "ol = octet_length n"
  using assms bitLen2octLen1 by blast 

lemma bit_len_comp:
  assumes "bit_length a < bit_length b"
  shows   "a < b"
  using assms word_len_comp by blast

lemma bit_len_head:
  assumes "bl = bit_length n"   "ol = octet_length n"   "os = nat_to_octets n" 
          "0 < n"   "hl = bit_length (hd os)"
  shows   "bl = 8*(ol - 1) + hl"
proof - 
  have 2: "(256::nat) = 2^8" by fastforce
  have n1: "256^(ol-1) \<le> n \<and> n < 256^ol" 
    by (metis 2 assms(2,4) word_length_eq zero_less_numeral) 
  have n2: "2^(bl-1) \<le> n \<and> n < 2^bl"  using assms(1,4) bit_len_exact3 by blast 
  have ol1: "0 < ol"                   by (metis assms(4) neq0_conv less_one n1 power_0)  
  let ?h = "hd os"
  have h1: "?h < 256"
    by (metis ol1 2 assms(2,3) list.size(3) nat_to_words_valid neq0_conv word_length_def 
        words_valid_hd) 
  have h2: "0 < ?h"                     using high_word_pos2 assms(3,4) by simp
  have h3: "?h < 2^hl \<and> 2^(hl-1) \<le> ?h" using h2 assms(5) bit_len_exact3 by blast
  have h4: "?h = n div 256^(ol-1)" 
    by (smt (z3) One_nat_def Suc_leI cancel_comm_monoid_add_class.diff_cancel hd_Cons_tl 
        le_add_diff_inverse less_mult_imp_div_less list.size(3) mod_less nat_lowbnd_word_len 
        nat_to_words_nil_iff_zero2 neq0_conv nth_Cons_0 nth_word power_add power_one_right 
        zero_less_numeral 2 assms(2,3) nth_word2 word_length_def ol1 h1 n1)
  have bo1: "ol = numBits_to_numOctets bl" using assms(1,2,4) bitLen2octLen1 by presburger
  have bo2: "8*(ol-1) \<le> bl - 1" 
  proof (cases "bl mod 8 = 0")
    case True
    then show ?thesis using bo1 numBits_to_numOctets_def by force
  next
    case False
    then show ?thesis using bo1 numBits_to_numOctets_def by presburger
  qed
  have bo3: "8*(ol-1) < bl" 
    by (metis bo2 le_less_trans less_imp_diff_less less_not_refl2 linorder_neqE_nat n2) 
  have a11: "2^(bl - 1) div 256^(ol-1) \<le> n div 256^(ol-1)"  using n2 div_le_mono by presburger 
  have a12: "2^(bl-1) div 256^(ol-1) \<le> ?h"                  using a11 h4 by presburger
  have a13: "(2::nat)^(bl-1) div 256^(ol-1) = 2^(bl-1) div 2^(8*(ol-1))" by (metis 2 power_mult)
  have a14: "(2::nat)^(bl-1) div 2^(8*(ol-1)) = 2^((bl-1) - 8*(ol-1))" 
    by (metis bo2 power_diff_power_eq zero_neq_numeral) 
  let ?x = "bl - 8*(ol-1)"
  have a15: "2^(?x - 1) \<le> ?h"                               using a12 a13 a14 by force
  have a21: "n div 256^(ol-1) < 2^bl div 256^(ol-1)" 
    by (smt (verit, ccfv_threshold) n2 2 div_greater_zero_iff div_le_mono le_add_diff_inverse 
      less_mult_imp_div_less mult.commute n1 nat_less_le one_less_numeral_iff power_add power_diff 
      power_increasing_iff power_mult semiring_norm(76) zero_less_numeral zero_less_power)
  have a22: "?h < 2^bl div 256^(ol-1)"                           using a21 h4 by presburger
  have a23: "(2::nat)^bl div 256^(ol-1) = 2^bl div 2^(8*(ol-1))" by (metis 2 power_mult)
  have a24: "(2::nat)^bl div 2^(8*(ol-1)) = 2^?x" 
    by (metis bo3 less_imp_le_nat power_diff zero_neq_numeral)
  have a25: "?h < 2^?x"  using a22 a23 a24 by argo
  have a: "?x = hl"      by (metis bit_len_exact3 a15 a25 h3 h2) 
  show ?thesis           using a bo3 by fastforce
qed

lemma bit_len_bnd:
  assumes "bl = bit_length n"   "ol = octet_length n"    
  shows   "bl \<le> 8*ol"
proof (cases "ol = 0")
  case True
  then show ?thesis
    using assms(1,2) bit_len_zero_eq nat_to_words_nil_iff_zero2 by force 
next
  case False
  have "(256::nat) = 2^8" by simp 
  then show ?thesis 
    by (metis assms(1,2) less_bit_len2 word_length_eq2 power_mult zero_less_numeral)
qed

lemma bit_len_comp_head:
  assumes "octet_length a = octet_length b" "ha = hd (nat_to_octets a)" "hb = hd (nat_to_octets b)"
          "bit_length ha < bit_length hb" "0 < a"
  shows   "a < b"
proof - 
  let ?ol   = "octet_length a"
  let ?abl  = "bit_length a"
  let ?bbl  = "bit_length b"
  let ?habl = "bit_length ha"
  let ?hbbl = "bit_length hb"
  have 0: "0 < b" by (metis assms(1,5) nat_to_words_nil_iff_zero2 neq0_conv zero_less_numeral) 
  have 1: "?bbl = 8*(?ol - 1) + ?hbbl" using 0 bit_len_head assms(1,3) by blast
  have 2: "?abl = 8*(?ol - 1) + ?habl" using assms(2,5) bit_len_head by blast
  show ?thesis    using 1 2 assms(4) bit_len_comp by simp
qed

lemma octet_len_comp:
  assumes "octet_length a < octet_length b"
  shows   "a < b"
  by (meson assms word_len_comp)

lemma octet_len_comp_bit_len:
  assumes "octet_length a < octet_length b"
  shows   "bit_length a < bit_length b"
  by (metis (mono_tags, opaque_lifting) assms bitLen2octLen1 bit_len_zero_eq less_nat_zero_code 
      less_or_eq_imp_le linorder_neqE_nat not_less word_len_comp)

lemma bit_len_head2:
  assumes "0 < length os" "hd os < 2^hl" "ol = length os" "n = octets_to_nat os" "octets_valid os"
  shows   "bit_length n \<le> 8*(ol-1) + hl"
proof (cases "hd os = 0")
  case T0: True
  let ?oss = "words_strip_zero os"
  have T1: "length ?oss < ol" 
    by (metis T0 assms(1,3) diff_self_eq_0 drop_0 hd_conv_nth length_0_conv less_le
              strip_zero_drop strip_zero_head strip_zero_length) 
  have T2: "octet_length n = length ?oss"
    by (metis assms(4,5) word_length_def words_to_nat_to_strip_words words_valid_def)
  have T3: "octet_length n \<le> ol-1"  using T1 T2 by linarith
  show ?thesis  by (metis T3 add.commute bit_len_bnd le_add2 le_trans mult_le_mono2) 
next
  case F0: False
  have F1: "nat_to_octets n = os" 
    by (metis F0 assms(1,4,5) hd_conv_nth length_0_conv neq0_conv words_to_nat_to_words 
       words_valid_def zero_less_numeral) 
  have F2: "octet_length n = ol" using F1 assms(3) word_length_def by simp
  show ?thesis
    by (metis F1 F2 assms(2) bit_len_head bit_len_zero le_add2 le_add_same_cancel2 less_bit_len2 
              nat_add_left_cancel_le neq0_conv) 
qed

lemma setleftmost_bit_len:
  assumes "Y = SetLeftmostBits a b X"  "octets_valid X"  "n = octets_to_nat Y"  "X \<noteq> []" 
  shows   "bit_length n \<le> 8*((length Y) - 1) + (8 - (8*a - b))"
  by (metis SetLeftmostBits_def SetLeftmostBits_hd SetLeftmostBits_valid assms bit_len_head2 
           length_greater_0_conv list.simps(3))

lemma setleftmost_bit_len2:
  assumes "emLen = numBits_to_numOctets emBits"  "emLen = length X"  "X \<noteq> []" "octets_valid X"
          "Y = SetLeftmostBits emLen emBits X"   "n = octets_to_nat Y"
  shows   "bit_length n \<le> emBits"
proof - 
  have 0: "0 < emLen"        using assms(2,3) by fast
  have 1: "length Y = emLen" by (simp add: SetLeftmostBits_len assms(2,5)) 
  have 2: "bit_length n \<le> 8*(emLen - 1) + (8 - (8*emLen - emBits))"
    using 1 assms(3,4,5,6) setleftmost_bit_len by blast
  show ?thesis proof (cases "emBits mod 8 = 0")
    case T0: True
    have T1: "emLen = emBits div 8" using T0 assms(1) numBits_to_numOctets_def by presburger
    show ?thesis
      by (metis 2 Suc_leI T0 T1 add.commute assms(2,3) cancel_comm_monoid_add_class.diff_cancel 
          diff_is_0_eq diff_zero dvd_mult_div_cancel le_add_diff_inverse length_greater_0_conv 
          mod_0_imp_dvd mult_Suc_right plus_1_eq_Suc) 
  next
    case F0: False
    let ?m = "emBits mod 8"
    let ?d = "emBits div 8"
    have F1: "emLen = ?d + 1"      using F0 assms(1) numBits_to_numOctets_def by presburger
    have F2: "emBits = 8*?d + ?m"  by simp
    have F3: "8*emLen - emBits = 8*?d + 8 - 8*?d - ?m"
      by (metis F1 F2 diff_diff_left distrib_left_numeral mult.right_neutral)
    have F4: "8*emLen - emBits = 8 - ?m"    by (simp add: F3)
    have F5: "8 - (8*emLen - emBits) = ?m"  by (simp add: F4) 
    have F6: "8*(emLen - 1) + (8 - (8*emLen - emBits)) = emBits"
      using F1 F5 diff_add_inverse2 by presburger 
    show ?thesis  by (metis 2 F6) 
  qed
qed

lemma setleftmost_bit_len3:
  assumes "emLen = numBits_to_numOctets emBits"  "emLen = length Y"  "Y \<noteq> []" "octets_valid Y"
          "TestLeftmostBits emLen emBits Y"   "n = octets_to_nat Y"
  shows   "bit_length n \<le> emBits"
  by (metis SetTestLeftmostBits assms setleftmost_bit_len2)

lemma bit_len_shift:
  assumes "bit_length X = l"  "0 < X" 
  shows   "bit_length (X*2^n) = l + n"
  by (metis assms less_numeral_extra(1) power_one_right word_len_shift)

lemma bit_len_le_shift:
  assumes "bit_length X \<le> l"  
  shows   "bit_length (X*2^n) \<le> l + n"
  by (metis assms power_one_right word_len_le_shift zero_less_one)

lemma bit_len_shift_add:
  assumes "bit_length X = l"  "0 < X"  "a < 2^n"
  shows   "bit_length (X*2^n + a) = l + n"
  by (metis assms power_one_right word_len_shift_add zero_less_one)

lemma bit_len_mult1:
  assumes "bit_length A = l"  "bit_length B = k"  "0 < A" 
  shows   "bit_length (A*B) \<le> l + k"
  using assms word_len_mult1 by blast

lemma bit_len_mult2:
  assumes "bit_length A = l"  "bit_length B = k"  "0 < A"  "0 < B"
  shows   "l + k - 1 \<le> bit_length (A*B)"
  using assms word_len_mult2 by auto


section \<open>Word Conversions\<close>

text \<open>Different standards may be written for different word sizes.  Here we define functions 
convenient for converting between word sizes.\<close>

definition words_to_words :: "nat \<Rightarrow> words \<Rightarrow> nat \<Rightarrow> words" where
  "words_to_words w1 xs w2 = nat_to_words w2 (words_to_nat w1 xs)"

definition words_to_words_newLen :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "words_to_words_newLen w1 l w2 = 
  ( let x = w1*l in
    (if (w2 dvd x) then (x div w2) else ((x div w2)+1 )) )"

definition words_to_words_len :: "nat \<Rightarrow> words \<Rightarrow> nat \<Rightarrow> words" where
  "words_to_words_len w1 xs w2 =
  (let l      = length xs;
       newLen = words_to_words_newLen w1 l w2
   in
       nat_to_words_len w2 (words_to_nat w1 xs) newLen)"

lemma ws2ws_newLen:
  assumes "w2 dvd w1"
  shows   "words_to_words_newLen w1 l w2 = l*(w1 div w2)" 
  using assms words_to_words_newLen_def by auto

lemma ws2ws_nil [simp]: "words_to_words w1 [] w2 = []"
  by (simp add: words_to_words_def)

lemma ws2wsnL0 [simp]: "words_to_words_newLen w1 0 w2 = 0"
  by (simp add: words_to_words_newLen_def)

lemma ws2wsl_nil [simp]: "words_to_words_len w1 [] w2 = []"
  by (simp add: words_to_words_len_def)

lemma ws2wsnL_same: 
  assumes "0 < w"
  shows   "words_to_words_newLen w l w = l"
  by (simp add: assms words_to_words_newLen_def)

lemma ws2wsl_same: 
  assumes "words_valid w xs"  "0 < w"
  shows   "words_to_words_len w xs w = xs"
  using assms words_to_nat_to_words_len2 words_to_words_len_def ws2wsnL_same by presburger 

lemma ws2wsl_len:
  assumes "words_valid w1 xs"  "0 < w1"  "0 < w2"
  shows   "length (words_to_words_len w1 xs w2) = words_to_words_newLen w1 (length xs) w2"
proof - 
  let ?l  = "length xs"
  let ?nL = "words_to_words_newLen w1 ?l w2"
  let ?xn = "words_to_nat w1 xs" 
  have 1: "?xn < (2^w1)^?l"   using assms(1,2) words_to_nat_len_bnd words_valid_def by blast
  let ?z = "w1*?l"
  let ?zm = "?z mod w2"
  let ?zd = "?z div w2"
  have 2: "?z = ?zd*w2 + ?zm" using div_mod_decomp by blast 
  have 3: "?zm < w2"          using assms(3) by force
  have 4: "?z \<le> ?nL * w2"
  proof (cases "w2 dvd ?z")
  case True
    then show ?thesis by (simp add: words_to_words_newLen_def) 
  next
    case False
    then have "?nL = ?zd + 1"           using words_to_words_newLen_def by presburger
    then have "?zd*w2 +  w2 = ?nL * w2" by simp 
    then have "?zd*w2 + ?zm < ?nL * w2" using 3 by linarith
    then show ?thesis                   using 2 by linarith
  qed
  have 5: "?xn < (2^w2)^?nL" 
    by (metis 1 4 leD leI le_less_trans mult.commute nat_power_less_imp_less power_mult 
              zero_less_numeral) 
  have 6: "length (nat_to_words_len w2 ?xn ?nL) = ?nL" by (simp add: 5 nat_to_words_len_upbnd)
  show ?thesis  using 6 words_to_words_len_def by auto
qed

lemma ws2wsl_concat:
  assumes "w2 dvd w1"  "words_valid w1 ys"
  shows   "words_to_words_len w1 (xs @ ys) w2 = 
          (words_to_words_len w1 xs w2) @ (words_to_words_len w1 ys w2)"
proof - 
  let ?xl = "length xs"
  let ?xn = "words_to_nat w1 xs"
  let ?yl = "length ys" 
  let ?yn = "words_to_nat w1 ys"
  let ?m  = "w1 div w2"
  have 0: "?m*w2 = w1"   using assms(1) by simp
  have 1: "words_to_nat w1 (xs@ys) = ?xn*((2^w1)^?yl) + ?yn"
    using words_to_nat_concat by fast
  have 10: "words_to_nat w1 (xs@ys) = ?xn*((2^w2)^(?m*?yl)) + ?yn"
    by (metis 0 1 mult.commute power_mult)
  let ?zn = "words_to_nat w1 (xs@ys)"
  have 2: "?yn < (2^w1)^?yl"
    using assms(2) strip_zero_length words_strip0_to_nat_len_bnd2 words_valid_def by blast 
  have 20: "?yn < (2^w2)^(?m*?yl)" 
    by (metis 0 2 mult.commute power_mult) 
  have 3: "length (xs@ys) = ?xl + ?yl"  by simp
  let ?newLen = "words_to_words_newLen w1 (?xl + ?yl) w2" 
  have 30: "?newLen = ?m*?xl + ?m*?yl"
    using assms(1) ws2ws_newLen add_mult_distrib by force 
  let ?newLenx = "words_to_words_newLen w1 ?xl w2" 
  have 31: "?newLenx = ?m*?xl"
    by (simp add: assms(1) ws2ws_newLen) 
  let ?newLeny = "words_to_words_newLen w1 ?yl w2" 
  have 32: "?newLeny = ?m*?yl"
    by (simp add: assms(1) ws2ws_newLen) 
  have 4: "nat_to_words_len w2 (words_to_nat w1 (xs@ys)) ?newLen = 
            (nat_to_words_len w2 ?xn (?m*?xl)) @ (nat_to_words_len w2 ?yn (?m*?yl))"
    using 10 20 30 sum_to_words_len2 by fastforce 
  show ?thesis  using 3 4 31 32 words_to_words_len_def by presburger 
qed


lemma ws2ws_append0:
  assumes "w2 dvd w1"  "m = w1 div w2"  "0 < w1" 
  shows   "words_to_words_len w1 (xs @ [0]) w2 = (words_to_words_len w1 xs w2) @ (replicate m 0)"
proof - 
  have "words_valid w1 [0]" by (simp add: words_valid_cons words_valid_nil)
  then show ?thesis
    by (metis One_nat_def Suc_eq_plus1 append.right_neutral assms(1,2) diff_zero list.size(3,4)
              mult.commute mult.right_neutral nat_to_words_len_def one_word_to_nat 
              words_to_words_len_def ws2ws_newLen ws2wsl_concat zero_to_word) 
qed

end
