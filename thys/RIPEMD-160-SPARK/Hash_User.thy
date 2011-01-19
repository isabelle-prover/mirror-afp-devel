theory Hash_User
imports Hash_Specification Hash_Declaration

begin


lemma goal12'1: 
  assumes H1: " x__index__subtype__1__first'' = (0 :: int)
  "
  assumes H6: 
  " chain___default_rcd''
    (| h0'chain
       := ca__1''
    |)
    (| h1'chain
       := cb__1''
    |)
    (| h2'chain
       := cc__1''
    |)
    (| h3'chain
       := cd__1''
    |)
    (| h4'chain
       := ce__1''
    |)
    = round'
        ( chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( x'' x__index__subtype__1__first''
        )
  "
  shows " chain___default_rcd''
          (| h0'chain
             := ca__1''
          |)
          (| h1'chain
             := cb__1''
          |)
          (| h2'chain
             := cc__1''
          |)
          (| h3'chain
             := cd__1''
          |)
          (| h4'chain
             := ce__1''
          |)
          = rounds'
              ( chain___default_rcd''
                (| h0'chain
                   := (1732584193 :: int)
                |)
                (| h1'chain
                   := (4023233417 :: int)
                |)
                (| h2'chain
                   := (2562383102 :: int)
                |)
                (| h3'chain
                   := (271733878 :: int)
                |)
                (| h4'chain
                   := (3285377520 :: int)
                |)
              )
              ( x__index__subtype__1__first'' + (1 :: int) )
              x''
        " (is "?C1")
using H1 H6
by (simp add:
  rounds_def rmd_body_def round_def
  h_0_def h0_0_def h1_0_def h2_0_def h3_0_def h4_0_def)


lemma rounds_step:
  assumes "0 <= i"
  shows "rounds X b (Suc i) = round (X i) (rounds X b i)"
  by (simp add: rounds_def rmd_body_def)

lemma from_to_id: "from_chain (to_chain C) = C"
proof (cases C)
  fix a b c d e f::word32
  assume "C = (a, b, c, d, e)"
  thus ?thesis by (cases a) simp
qed

lemma steps_to_steps':
  "round X (foldl a b c) = round X (from_chain (to_chain (foldl a b c)))"
  unfolding from_to_id ..

lemma rounds'_step:
  assumes "0 <= i"
  shows "rounds' c (i + 1) x = round' (rounds' c i x) (x i)"
proof -
  have makesuc: "nat (i + 1) = Suc (nat i)" using assms by simp
  show ?thesis using assms
    by (simp add: makesuc rounds_def rmd_body_def steps_to_steps')
qed

lemma goal13'1:
  assumes "0 <= loop__1__i''"
  assumes H1: 
  " chain___default_rcd''
    (| h0'chain
       := ca''
    |)
    (| h1'chain
       := cb''
    |)
    (| h2'chain
       := cc''
    |)
    (| h3'chain
       := cd''
    |)
    (| h4'chain
       := ce''
    |)
    = rounds'
        ( chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( loop__1__i'' + (1 :: int) )
        x''
  "
  assumes H18: 
  " chain___default_rcd''
    (| h0'chain
       := ca__1''
    |)
    (| h1'chain
       := cb__1''
    |)
    (| h2'chain
       := cc__1''
    |)
    (| h3'chain
       := cd__1''
    |)
    (| h4'chain
       := ce__1''
    |)
    = round'
        ( chain___default_rcd''
          (| h0'chain
             := ca''
          |)
          (| h1'chain
             := cb''
          |)
          (| h2'chain
             := cc''
          |)
          (| h3'chain
             := cd''
          |)
          (| h4'chain
             := ce''
          |)
        )
        ( x'' ( loop__1__i'' + (1 :: int) )
        )
  "
  shows " chain___default_rcd''
          (| h0'chain
             := ca__1''
          |)
          (| h1'chain
             := cb__1''
          |)
          (| h2'chain
             := cc__1''
          |)
          (| h3'chain
             := cd__1''
          |)
          (| h4'chain
             := ce__1''
          |)
          = rounds'
              ( chain___default_rcd''
                (| h0'chain
                   := (1732584193 :: int)
                |)
                (| h1'chain
                   := (4023233417 :: int)
                |)
                (| h2'chain
                   := (2562383102 :: int)
                |)
                (| h3'chain
                   := (271733878 :: int)
                |)
                (| h4'chain
                   := (3285377520 :: int)
                |)
              )
              ( loop__1__i'' + (2 :: int) )
              x''
        "
proof -
  have loop_suc: "loop__1__i'' + 2 = (loop__1__i'' + 1) + 1" by simp
  have "0 <= loop__1__i'' + 1" using `0 <= loop__1__i''` by simp
  show ?thesis
    unfolding loop_suc
    unfolding rounds'_step[OF `0 <= loop__1__i'' + 1`]
    unfolding H1[symmetric]
    unfolding H18 ..
qed


lemma goal17'1:
  assumes H1: 
  " chain___default_rcd''
    (| h0'chain
       := ca''
    |)
    (| h1'chain
       := cb''
    |)
    (| h2'chain
       := cc''
    |)
    (| h3'chain
       := cd''
    |)
    (| h4'chain
       := ce''
    |)
    = rounds'
        ( chain___default_rcd''
          (| h0'chain
             := (1732584193 :: int)
          |)
          (| h1'chain
             := (4023233417 :: int)
          |)
          (| h2'chain
             := (2562383102 :: int)
          |)
          (| h3'chain
             := (271733878 :: int)
          |)
          (| h4'chain
             := (3285377520 :: int)
          |)
        )
        ( x__index__subtype__1__last'' + (1 :: int) )
        x''
  "
  shows " chain___default_rcd''
          (| h0'chain
             := ca''
          |)
          (| h1'chain
             := cb''
          |)
          (| h2'chain
             := cc''
          |)
          (| h3'chain
             := cd''
          |)
          (| h4'chain
             := ce''
          |)
          = rmd_hash'
              x''
              ( x__index__subtype__1__last'' + (1 :: int) )
        "
unfolding rmd_def H1 rounds_def ..


lemmas userlemmas = goal12'1 goal13'1 goal17'1
end
