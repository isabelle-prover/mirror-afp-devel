section "Verification of $hash$"
theory Hash_Specification
imports Hash_Declaration Global_Specification

begin

abbreviation from_chain :: "chain' => chain" where
  "from_chain c == (
    word_of_int (h0'chain c),
    word_of_int (h1'chain c),
    word_of_int (h2'chain c),
    word_of_int (h3'chain c),
    word_of_int (h4'chain c))"

abbreviation to_chain :: "chain => chain'" where
  "to_chain c ==
    (let (h0, h1, h2, h3, h4) = c in
      chain___default_rcd''
      (|h0'chain := uint h0,
        h1'chain := uint h1,
        h2'chain := uint h2,
        h3'chain := uint h3,
        h4'chain := uint h4|))"

abbreviation round' :: " [ chain' , block' ] => chain' " where
  "round' c b == to_chain (round (%n. word_of_int (b (int n))) (from_chain c))"

abbreviation rounds' :: " [ chain' , int , message' ] => chain' " where
  "rounds' h i X ==
     to_chain (rounds
      (\<lambda>n. \<lambda>m. word_of_int (X (int n) (int m)))
      (from_chain h)
      (nat i))"

abbreviation rmd_hash' :: " [ message' , int ] => chain' " where
  "rmd_hash' X i == to_chain (rmd
    (\<lambda>n. \<lambda>m. word_of_int (X (int n) (int m)))
    (nat i))"

end
