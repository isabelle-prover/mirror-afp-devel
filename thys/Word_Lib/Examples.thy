theory Examples
  imports Bitwise
begin

type_synonym word32 = "32 word"

text "proofs using bitwise expansion"

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
  by word_bitwise

lemma "(x AND NOT 3) >> 4 << 2 = ((x >> 2) AND NOT 3)"
  for x :: "10 word"
  by word_bitwise

lemma "((x AND -8) >> 3) AND 7 = (x AND 56) >> 3"
  for x :: "12 word"
  by word_bitwise

text "some problems require further reasoning after bit expansion"

lemma "x \<le> 42 \<Longrightarrow> x \<le> 89"
  for x :: "8 word"
  apply word_bitwise
  apply blast
  done

lemma "(x AND 1023) = 0 \<Longrightarrow> x \<le> -1024"
  for x :: word32
  apply word_bitwise
  apply clarsimp
  done

text "operations like shifts by non-numerals will expose some internal list
 representations but may still be easy to solve"

lemma shiftr_overflow: "32 \<le> a \<Longrightarrow> b >> a = 0"
  for b :: word32
  apply word_bitwise
  apply simp
  done

end