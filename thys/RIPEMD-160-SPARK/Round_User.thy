theory Round_User
imports Round_Specification Round_Declaration

begin


lemma uint_word_of_int_id:
  assumes "0 <= (x::int)"
  assumes "x <= 4294967295"
  shows"uint(word_of_int x::word32) = x"
  unfolding int_word_uint
  using assms
  by (simp add:int_mod_eq')

lemma steps_step: "steps X cc (Suc i) = step_both X (steps X cc i) i"
  unfolding steps_def
  by (induct i) simp_all

lemma from_to_id: "from_chain_pair (to_chain_pair CC) = CC"
proof (cases CC)
  fix a::chain
  fix b c d e f::word32
  assume "CC = (a, b, c, d, e, f)"
  thus ?thesis by (cases a) simp
qed

lemma steps_to_steps':
  "F A (steps X cc i) B =
   F A (from_chain_pair (to_chain_pair (steps X cc i))) B"
  unfolding from_to_id ..

lemma steps'_step:
  assumes "0 <= i"
  shows
  "steps' cc (i + 1) X = to_chain_pair (
     step_both
       (\<lambda>n. word_of_int (X (int n)))
       (from_chain_pair (steps' cc i X))
       (nat i))"
proof -
  have "nat (i + 1) = Suc (nat i)" using assms by simp
  show ?thesis
    unfolding `nat (i + 1) = Suc (nat i)` steps_step steps_to_steps'
    ..
qed 

lemma step_from_hyp:
  fixes a b c d e
  fixes a' b' c' d' e'
  fixes a_0 b_0 c_0 d_0 e_0
  fixes x
  fixes j
  assumes
  step_hyp:
  "chain_pair___default_rcd''
     \<lparr>left'chain_pair := chain___default_rcd''
        \<lparr>h0'chain := a, h1'chain := b, h2'chain := c, h3'chain := d,
         h4'chain := e\<rparr>,
      right'chain_pair := chain___default_rcd''
        \<lparr>h0'chain := a', h1'chain := b', h2'chain := c', h3'chain := d',
         h4'chain := e'\<rparr>\<rparr> =
   steps'
     (chain_pair___default_rcd''
        \<lparr>left'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := a_0, h1'chain := b_0, h2'chain := c_0,
            h3'chain := d_0, h4'chain := e_0\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := a_0, h1'chain := b_0, h2'chain := c_0,
            h3'chain := d_0, h4'chain := e_0\<rparr>\<rparr>)
     j x"
  assumes a_borders:  "0 <= a " "a <= 4294967295" (is "_ <= ?M")
  assumes b_borders:  "0 <= b " "b  <= ?M"
  assumes c_borders:  "0 <= c " "c  <= ?M"
  assumes d_borders:  "0 <= d " "d  <= ?M"
  assumes e_borders:  "0 <= e " "e  <= ?M"
  assumes a'_borders: "0 <= a'" "a' <= ?M"
  assumes b'_borders: "0 <= b'" "b' <= ?M"
  assumes c'_borders: "0 <= c'" "c' <= ?M"
  assumes d'_borders: "0 <= d'" "d' <= ?M"
  assumes e'_borders: "0 <= e'" "e' <= ?M"
  assumes x_borders: "0 <= x (r_l' j)" "x (r_l' j) <= ?M"
                     "0 <= x (r_r' j)" "x (r_r' j) <= ?M"
  assumes j_borders: "0 <= j" "j <= 79"
  shows
  "chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := e,
          h1'chain :=
            (wordops__rotate_left' (s_l' j)
              ((((a + f' j b c d) mod 4294967296 +
                 x (r_l' j)) mod
                4294967296 +
                k_l' j) mod
               4294967296) +
             e) mod
            4294967296,
          h2'chain := b, h3'chain := wordops__rotate_left' 10 c,
          h4'chain := d\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := e',
            h1'chain :=
              (wordops__rotate_left' (s_r' j)
                ((((a' + f' (79 - j) b' c' d') mod
                   4294967296 +
                   x (r_r' j)) mod
                  4294967296 +
                  k_r' j) mod
                 4294967296) +
               e') mod
              4294967296,
            h2'chain := b', h3'chain := wordops__rotate_left' 10 c',
            h4'chain := d'\<rparr>\<rparr> =
    steps'
     (chain_pair___default_rcd''
      \<lparr>left'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := a_0, h1'chain := b_0, h2'chain := c_0,
            h3'chain := d_0, h4'chain := e_0\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := a_0, h1'chain := b_0, h2'chain := c_0,
              h3'chain := d_0, h4'chain := e_0\<rparr>\<rparr>)
     (j + 1) x"
proof -
  let ?MM = 4294967296
  have AL: "uint(word_of_int e::word32) = e"
    by (rule uint_word_of_int_id[OF `0 <= e` `e <= ?M`])
  have CL: "uint(word_of_int b::word32) = b"
    by (rule uint_word_of_int_id[OF `0 <= b` `b <= ?M`])
  have DL: "True" ..
  have EL: "uint(word_of_int d::word32) = d"
    by (rule uint_word_of_int_id[OF `0 <= d` `d <= ?M`])
  have AR: "uint(word_of_int e'::word32) = e'"
    by (rule uint_word_of_int_id[OF `0 <= e'` `e' <= ?M`])
  have CR: "uint(word_of_int b'::word32) = b'"
    by (rule uint_word_of_int_id[OF `0 <= b'` `b' <= ?M`])
  have DR: "True" ..
  have ER: "uint(word_of_int d'::word32) = d'"
    by (rule uint_word_of_int_id[OF `0 <= d'` `d' <= ?M`])
  have BL: "(uint
      (word_rotl (s (nat j))
        ((word_of_int::int\<Rightarrow>word32)
          ((((a + f' j b c d) mod 4294967296 +
             x (r_l' j)) mod
            4294967296 +
            k_l' j) mod
           4294967296))) +
     e) mod
    4294967296 =
    uint
     (word_rotl (s (nat j))
       (word_of_int a +
        f (nat j) (word_of_int b) (word_of_int c) (word_of_int d) +
        word_of_int (x (r_l' j)) +
        K (nat j)) +
      word_of_int e)"
    (is "(uint (word_rotl _ (_ ((((_ + ?F) mod _ + ?X) mod _ + _) mod _))) + _)
          mod _ = _")
  proof -
    have "a mod ?MM = a" using `0 <= a` `a <= ?M`
      by (simp add: int_mod_eq')
    have "?X mod ?MM = ?X" using `0 <= ?X` `?X <= ?M`
      by (simp add: int_mod_eq')
    have "e mod ?MM = e" using `0 <= e` `e <= ?M`
      by (simp add: int_mod_eq')
    have "(?MM::int) = 2 ^ len_of TYPE(32)" by simp
    show ?thesis
      unfolding
        word_add_def
        uint_word_of_int_id[OF `0 <= a` `a <= ?M`]
        uint_word_of_int_id[OF `0 <= ?X` `?X <= ?M`]
        int_word_uint
      unfolding `?MM = 2 ^ len_of TYPE(32)`
      unfolding word_uint.Abs_norm
      by (simp add:
        `a mod ?MM = a`
        `e mod ?MM = e`
        `?X mod ?MM = ?X`)
  qed

  have BR: "(uint
      (word_rotl (s' (nat j))
        ((word_of_int::int\<Rightarrow>word32)
          ((((a' + f' (79 - j) b' c' d') mod
             4294967296 +
             x (r_r' j)) mod
            4294967296 +
            k_r' j) mod
           4294967296))) +
     e') mod
    4294967296 =
    uint
     (word_rotl (s' (nat j))
       (word_of_int a' +
        f (79 - nat j) (word_of_int b') (word_of_int c') (word_of_int d') +
        word_of_int (x (r_r' j)) +
        K' (nat j)) +
      word_of_int e')"
    (is "(uint (word_rotl _ (_ ((((_ + ?F) mod _ + ?X) mod _ + _) mod _))) + _)
          mod _ = _")
  proof -
    have "a' mod ?MM = a'" using `0 <= a'` `a' <= ?M`
      by (simp add: int_mod_eq')
    have "?X mod ?MM = ?X" using `0 <= ?X` `?X <= ?M`
      by (simp add: int_mod_eq')
    have "e' mod ?MM = e'" using `0 <= e'` `e' <= ?M`
      by (simp add: int_mod_eq')
    have "(?MM::int) = 2 ^ len_of TYPE(32)" by simp
    have nat_transfer: "79 - nat j = nat (79 - j)"
      using nat_diff_distrib `0 <= j`  `j <= 79`
      by simp
    show ?thesis
      unfolding
        word_add_def
        uint_word_of_int_id[OF `0 <= a'` `a' <= ?M`]
        uint_word_of_int_id[OF `0 <= ?X` `?X <= ?M`]
        int_word_uint
        nat_transfer
      unfolding `?MM = 2 ^ len_of TYPE(32)`
      unfolding word_uint.Abs_norm
      by (simp add: 
        `a' mod ?MM = a'`
        `e' mod ?MM = e'`
        `?X mod ?MM = ?X`)
  qed

  show ?thesis
    unfolding steps'_step[OF `0 <= j`] step_hyp[symmetric]
      step_both_def step_r_def step_l_def
    by (simp add: AL BL CL DL EL AR BR CR DR ER)
qed    

abbreviation
  "f_0_result == (((ca'' + f_spark' 0 cb'' cc'' cd'') mod 4294967296 +
        x'' (r_l_spark' 0)) mod 4294967296 + k_l_spark' 0) mod 4294967296"
abbreviation
  "f_79_result == (((ca'' + f_spark' 79 cb'' cc'' cd'') mod 4294967296 +
        x'' (r_r_spark' 0)) mod 4294967296 + k_r_spark' 0) mod 4294967296"

lemma goal61'1:
  assumes ca_borders: "0 <= ca''" "ca'' <= 4294967295" (is "_ <= ?M")
  assumes cb_borders: "0 <= cb''" "cb'' <= ?M"
  assumes cc_borders: "0 <= cc''" "cc'' <= ?M"
  assumes cd_borders: "0 <= cd''" "cd'' <= ?M"
  assumes ce_borders: "0 <= ce''" "ce'' <= ?M"
  assumes r_l_0_borders: "0 <= r_l_spark' 0" "r_l_spark' 0 <= 15"
  assumes r_r_0_borders: "0 <= r_r_spark' 0" "r_r_spark' 0 <= 15"
  assumes returns:
  "wordops__rotate' (s_l_spark' 0) f_0_result =
    wordops__rotate_left' (s_l_spark' 0) f_0_result"
  "wordops__rotate' (s_r_spark' 0) f_79_result =
    wordops__rotate_left' (s_r_spark' 0) f_79_result"
  "wordops__rotate' 10 cc'' = wordops__rotate_left' 10 cc''"
  "f_spark' 0 cb'' cc'' cd'' = f' 0 cb'' cc'' cd''"
  "f_spark' 79 cb'' cc'' cd'' = f' 79 cb'' cc'' cd''"
  "k_l_spark' 0 = k_l' 0"
  "k_r_spark' 0 = k_r' 0"
  "r_l_spark' 0 = r_l' 0"
  "r_r_spark' 0 = r_r' 0"
  "s_l_spark' 0 = s_l' 0"
  "s_r_spark' 0 = s_r' 0"
assumes x_borders: " \<forall>i. 0 \<le> i \<and> i \<le> 15 \<longrightarrow> 0 \<le> x'' i \<and> x'' i \<le> ?M"
shows "chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := ce'',
          h1'chain :=
            (wordops__rotate' (s_l_spark' 0)
              ((((ca'' + f_spark' 0 cb'' cc'' cd'') mod 4294967296 +
                 x'' (r_l_spark' 0)) mod
                4294967296 +
                k_l_spark' 0) mod
               4294967296) +
             ce'') mod
            4294967296,
          h2'chain := cb'', h3'chain := wordops__rotate' 10 cc'',
          h4'chain := cd''\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ce'',
            h1'chain :=
              (wordops__rotate' (s_r_spark' 0)
                ((((ca'' + f_spark' 79 cb'' cc'' cd'') mod 4294967296 +
                   x'' (r_r_spark' 0)) mod
                  4294967296 +
                  k_r_spark' 0) mod
                 4294967296) +
               ce'') mod
              4294967296,
            h2'chain := cb'', h3'chain := wordops__rotate' 10 cc'',
            h4'chain := cd''\<rparr>\<rparr> =
    steps'
     (chain_pair___default_rcd''
      \<lparr>left'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
            h3'chain := cd'', h4'chain := ce''\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
              h3'chain := cd'', h4'chain := ce''\<rparr>\<rparr>)
     1 x''"
proof -
  have step_hyp:
  "chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
          h3'chain := cd'', h4'chain := ce''\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
            h3'chain := cd'', h4'chain := ce''\<rparr>\<rparr> =
    steps'
     (chain_pair___default_rcd''
      \<lparr>left'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
            h3'chain := cd'', h4'chain := ce''\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := ca'', h1'chain := cb'', h2'chain := cc'',
              h3'chain := cd'', h4'chain := ce''\<rparr>\<rparr>)
     0 x''"
    unfolding steps_def
    by (simp add:
      uint_word_of_int_id[OF ca_borders]
      uint_word_of_int_id[OF cb_borders]
      uint_word_of_int_id[OF cc_borders]
      uint_word_of_int_id[OF cd_borders]
      uint_word_of_int_id[OF ce_borders])

  from r_l_0_borders x_borders
  have "0 \<le> x'' (r_l_spark' 0)" by blast
  hence x_lower: "0 <= x'' (r_l' 0)" unfolding returns .

  from r_l_0_borders x_borders x_borders
  have "x'' (r_l_spark' 0) <= ?M" by blast
  hence x_upper: "x'' (r_l' 0) <= ?M" unfolding returns .

  from r_r_0_borders x_borders
  have "0 \<le> x'' (r_r_spark' 0)" by blast
  hence x_lower': "0 <= x'' (r_r' 0)" unfolding returns .

  from r_r_0_borders x_borders
  have "x'' (r_r_spark' 0) <= ?M" by blast
  hence x_upper': "x'' (r_r' 0) <= ?M" unfolding returns .

  have "0 <= (0::int)" by simp
  have "0 <= (79::int)" by simp
  note step_from_hyp [OF
    step_hyp
    ca_borders  cb_borders  cc_borders  cd_borders  ce_borders
    ca_borders  cb_borders  cc_borders  cd_borders  ce_borders
  ]
  note this[OF x_lower x_upper x_lower' x_upper' `0 <= 0` `0 <= 79`]
  thus ?thesis unfolding returns(1) returns(2) unfolding returns
    by simp
qed

abbreviation "rotate_arg_l ==
    ((((cla'' + f_spark' (loop__1__j'' + 1) clb'' clc'' cld'') mod 4294967296 +
         x'' (r_l_spark' (loop__1__j'' + 1))) mod 4294967296 +
         k_l_spark' (loop__1__j'' + 1)) mod 4294967296)"
abbreviation "rotate_arg_r ==((((cra'' + f_spark' (79 - (loop__1__j'' + 1)) crb'' crc'' crd'') mod
         4294967296 + x'' (r_r_spark' (loop__1__j'' + 1))) mod 4294967296 +
         k_r_spark' (loop__1__j'' + 1)) mod 4294967296)"


lemma goal62'1:
  assumes cla_borders: "0 <= cla''" "cla'' <= 4294967295" (is "_ <= ?M")
  assumes clb_borders: "0 <= clb''" "clb'' <= ?M"
  assumes clc_borders: "0 <= clc''" "clc'' <= ?M"
  assumes cld_borders: "0 <= cld''" "cld'' <= ?M"
  assumes cle_borders: "0 <= cle''" "cle'' <= ?M"
  assumes cra_borders: "0 <= cra''" "cra'' <= ?M"
  assumes crb_borders: "0 <= crb''" "crb'' <= ?M"
  assumes crc_borders: "0 <= crc''" "crc'' <= ?M"
  assumes crd_borders: "0 <= crd''" "crd'' <= ?M"
  assumes cre_borders: "0 <= cre''" "cre'' <= ?M"
  assumes step_hyp:
  "chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := cla'', h1'chain := clb'', h2'chain := clc'',
          h3'chain := cld'', h4'chain := cle''\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := cra'', h1'chain := crb'', h2'chain := crc'',
          h3'chain := crd'', h4'chain := cre''\<rparr>\<rparr> =
      steps'
   (chain_pair___default_rcd''
      \<lparr>left'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca___init'', h1'chain := cb___init'',
            h2'chain := cc___init'', h3'chain := cd___init'',
            h4'chain := ce___init''\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := ca___init'', h1'chain := cb___init'',
              h2'chain := cc___init'', h3'chain := cd___init'',
              h4'chain := ce___init''\<rparr>\<rparr>)
     (loop__1__j'' + 1) x''"
  assumes returns:
    "wordops__rotate' (s_l_spark' (loop__1__j'' + 1)) rotate_arg_l =
     wordops__rotate_left' (s_l_spark' (loop__1__j'' + 1)) rotate_arg_l"
    "wordops__rotate' (s_r_spark' (loop__1__j'' + 1)) rotate_arg_r =
     wordops__rotate_left' (s_r_spark' (loop__1__j'' + 1)) rotate_arg_r"
    "f_spark' (loop__1__j'' + 1) clb'' clc'' cld'' =
     f' (loop__1__j'' + 1) clb'' clc'' cld''"
    "f_spark' (78 - loop__1__j'') crb'' crc'' crd'' =
     f' (78 - loop__1__j'') crb'' crc'' crd''" (*[simplified s]*)
    "wordops__rotate' 10 clc'' = wordops__rotate_left' 10 clc''"
    "wordops__rotate' 10 crc'' = wordops__rotate_left' 10 crc''"
    "k_l_spark' (loop__1__j'' + 1) = k_l' (loop__1__j'' + 1)"
    "k_r_spark' (loop__1__j'' + 1) = k_r' (loop__1__j'' + 1)"
    "r_l_spark' (loop__1__j'' + 1) = r_l' (loop__1__j'' + 1)"
    "r_r_spark' (loop__1__j'' + 1) = r_r' (loop__1__j'' + 1)"
    "s_l_spark' (loop__1__j'' + 1) = s_l' (loop__1__j'' + 1)"
    "s_r_spark' (loop__1__j'' + 1) = s_r' (loop__1__j'' + 1)"
  assumes x_borders: "\<forall>i. 0 \<le> i \<and> i \<le> 15 \<longrightarrow> 0 \<le> x'' i \<and> x'' i \<le> ?M"
  assumes r_l_borders:
    "0 <= r_l_spark' (loop__1__j'' + 1)" "r_l_spark' (loop__1__j'' + 1) <= 15"
  assumes r_r_borders:
    "0 <= r_r_spark' (loop__1__j'' + 1)" "r_r_spark' (loop__1__j'' + 1) <= 15"
  assumes j_loop_1_borders: "0 <= loop__1__j''" "loop__1__j'' <= 78"
  shows "chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := cle'',
          h1'chain :=
            (wordops__rotate' (s_l_spark' (loop__1__j'' + 1))
              ((((cla'' + f_spark' (loop__1__j'' + 1) clb'' clc'' cld'') mod
                 4294967296 +
                 x'' (r_l_spark' (loop__1__j'' + 1))) mod
                4294967296 +
                k_l_spark' (loop__1__j'' + 1)) mod
               4294967296) +
             cle'') mod
            4294967296,
          h2'chain := clb'', h3'chain := wordops__rotate' 10 clc'',
          h4'chain := cld''\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := cre'',
            h1'chain :=
              (wordops__rotate' (s_r_spark' (loop__1__j'' + 1))
                ((((cra'' +
                    f_spark' (79 - (loop__1__j'' + 1)) crb'' crc''
                     crd'') mod
                   4294967296 +
                   x'' (r_r_spark' (loop__1__j'' + 1))) mod
                  4294967296 +
                  k_r_spark' (loop__1__j'' + 1)) mod
                 4294967296) +
               cre'') mod
              4294967296,
            h2'chain := crb'', h3'chain := wordops__rotate' 10 crc'',
            h4'chain := crd''\<rparr>\<rparr> =
    steps'
     (chain_pair___default_rcd''
      \<lparr>left'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca___init'', h1'chain := cb___init'',
            h2'chain := cc___init'', h3'chain := cd___init'',
            h4'chain := ce___init''\<rparr>,
         right'chain_pair := chain___default_rcd''
           \<lparr>h0'chain := ca___init'', h1'chain := cb___init'',
              h2'chain := cc___init'', h3'chain := cd___init'',
              h4'chain := ce___init''\<rparr>\<rparr>)
     (loop__1__j'' + 2) x''"
proof -
  have s: "78 - loop__1__j'' = (79 - (loop__1__j'' + 1))" by simp

  from r_l_borders x_borders
  have "0 \<le> x'' (r_l_spark' (loop__1__j'' + 1))" by blast
  hence x_lower: "0 <= x'' (r_l' (loop__1__j'' + 1))" unfolding returns .

  from r_l_borders x_borders
  have "x'' (r_l_spark' (loop__1__j'' + 1)) <= ?M" by blast
  hence x_upper: "x'' (r_l' (loop__1__j'' + 1)) <= ?M" unfolding returns .

  from r_r_borders x_borders
  have "0 \<le> x'' (r_r_spark' (loop__1__j'' + 1))" by blast
  hence x_lower': "0 <= x'' (r_r' (loop__1__j'' + 1))" unfolding returns .

  from r_r_borders x_borders
  have "x'' (r_r_spark' (loop__1__j'' + 1)) <= ?M" by blast
  hence x_upper': "x'' (r_r' (loop__1__j'' + 1)) <= ?M" unfolding returns .

  from j_loop_1_borders have "0 <= loop__1__j'' + 1" by simp
  from j_loop_1_borders have "loop__1__j'' + 1 <= 79" by simp

  have "loop__1__j'' + 1 + 1 = loop__1__j'' + 2" by simp

  have "f' (79 - (loop__1__j'' + 1)) crb'' crc'' crd'' =
    f_spark' (79 - (loop__1__j'' + 1)) crb'' crc'' crd''"
    using returns by simp
  note returns = returns this

  note step_from_hyp[OF step_hyp
    cla_borders
    clb_borders
    clc_borders
    cld_borders
    cle_borders
    cra_borders
    crb_borders
    crc_borders
    crd_borders
    cre_borders]
  from this[OF 
    x_lower x_upper x_lower' x_upper'
    `0 <= loop__1__j'' + 1` `loop__1__j'' + 1 <= 79`]
  show ?thesis unfolding `loop__1__j'' + 1 + 1 = loop__1__j'' + 2`
    unfolding returns(1) returns(2) unfolding returns
    by simp
qed

abbreviation "INIT_CHAIN == chain___default_rcd''
      \<lparr>h0'chain := ca___init'', h1'chain := cb___init'',
         h2'chain := cc___init'', h3'chain := cd___init'',
         h4'chain := ce___init''\<rparr>"

lemma goal76'1:
  assumes cla_borders: "0 <= cla''" "cla'' <= 4294967295" (is "_ <= ?M")
  assumes clb_borders: "0 <= clb''" "clb'' <= ?M"
  assumes clc_borders: "0 <= clc''" "clc'' <= ?M"
  assumes cld_borders: "0 <= cld''" "cld'' <= ?M"
  assumes cle_borders: "0 <= cle''" "cle'' <= ?M"
  assumes cra_borders: "0 <= cra''" "cra'' <= ?M"
  assumes crb_borders: "0 <= crb''" "crb'' <= ?M"
  assumes crc_borders: "0 <= crc''" "crc'' <= ?M"
  assumes crd_borders: "0 <= crd''" "crd'' <= ?M"
  assumes cre_borders: "0 <= cre''" "cre'' <= ?M"
  assumes ca_init_borders: "0 <= ca___init''" "ca___init'' <= ?M"
  assumes cb_init_borders: "0 <= cb___init''" "cb___init'' <= ?M"
  assumes cc_init_borders: "0 <= cc___init''" "cc___init'' <= ?M"
  assumes cd_init_borders: "0 <= cd___init''" "cd___init'' <= ?M"
  assumes ce_init_borders: "0 <= ce___init''" "ce___init'' <= ?M"
  assumes step_hyp:
  "chain_pair___default_rcd''
  \<lparr>left'chain_pair := chain___default_rcd''
     \<lparr>h0'chain := cla'', h1'chain := clb'', h2'chain := clc'', h3'chain := cld'', h4'chain := cle''\<rparr>,
     right'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := cra'', h1'chain := crb'', h2'chain := crc'', h3'chain := crd'', h4'chain := cre''\<rparr>\<rparr> =
  steps'
   (chain_pair___default_rcd''
    \<lparr>left'chain_pair := chain___default_rcd''
       \<lparr>h0'chain := ca___init'', h1'chain := cb___init'', h2'chain := cc___init'', h3'chain := cd___init'',
          h4'chain := ce___init''\<rparr>,
       right'chain_pair := chain___default_rcd''
         \<lparr>h0'chain := ca___init'', h1'chain := cb___init'', h2'chain := cc___init'', h3'chain := cd___init'',
            h4'chain := ce___init''\<rparr>\<rparr>)
   80 x''"
  shows "chain___default_rcd''
    \<lparr>h0'chain := ((cb___init'' + clc'') mod 4294967296 + crd'') mod 4294967296,
       h1'chain := ((cc___init'' + cld'') mod 4294967296 + cre'') mod 4294967296,
       h2'chain := ((cd___init'' + cle'') mod 4294967296 + cra'') mod 4294967296,
       h3'chain := ((ce___init'' + cla'') mod 4294967296 + crb'') mod 4294967296,
       h4'chain := ((ca___init'' + clb'') mod 4294967296 + crc'') mod 4294967296\<rparr> =
    round'
     (chain___default_rcd''
      \<lparr>h0'chain := ca___init'', h1'chain := cb___init'', h2'chain := cc___init'', h3'chain := cd___init'',
         h4'chain := ce___init''\<rparr>)
     x''"
proof -
  have steps_to_steps':
    "steps
       (\<lambda>n\<Colon>nat. word_of_int (x'' (int n)))
       (from_chain INIT_CHAIN, from_chain INIT_CHAIN)
       80 =
    from_chain_pair (
      steps'
      (chain_pair___default_rcd''
        \<lparr>left'chain_pair := INIT_CHAIN, right'chain_pair := INIT_CHAIN\<rparr>)
      80
      x'')"
    unfolding from_to_id by simp
  show ?thesis
    unfolding round_def
    unfolding steps_to_steps'
    unfolding step_hyp[symmetric]
    by (simp add: uint_word_ariths(1) rdmods
      uint_word_of_int_id[OF ca_init_borders]
      uint_word_of_int_id[OF cb_init_borders]
      uint_word_of_int_id[OF cc_init_borders]
      uint_word_of_int_id[OF cd_init_borders]
      uint_word_of_int_id[OF ce_init_borders]
      uint_word_of_int_id[OF cla_borders]
      uint_word_of_int_id[OF clb_borders]
      uint_word_of_int_id[OF clc_borders]
      uint_word_of_int_id[OF cld_borders]
      uint_word_of_int_id[OF cle_borders]
      uint_word_of_int_id[OF cra_borders]
      uint_word_of_int_id[OF crb_borders]
      uint_word_of_int_id[OF crc_borders]
      uint_word_of_int_id[OF crd_borders]
      uint_word_of_int_id[OF cre_borders])
qed

lemmas userlemmas = goal61'1 goal62'1 goal76'1

end
