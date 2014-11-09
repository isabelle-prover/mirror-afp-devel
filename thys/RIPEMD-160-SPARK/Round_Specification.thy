section "Verification of $round$"
theory Round_Specification
imports Global_Specification Round_Declaration

begin

abbreviation bit__and' :: " [ int , int ] => int " where
  "bit__and' == Global_Specification.bit__and'"
abbreviation bit__or' :: " [ int , int ] => int " where
  "bit__or' == Global_Specification.bit__or'"
abbreviation bit__xor' :: " [ int , int ] => int " where
  "bit__xor' == Global_Specification.bit__xor'"
abbreviation f' :: " [ int , int , int , int ] => int " where
  "f' == Global_Specification.f'"
abbreviation k_l' :: " int => int " where
  "k_l' == Global_Specification.k_l'"
abbreviation k_r' :: " int => int " where
  "k_r' == Global_Specification.k_r'"
abbreviation r_l' :: " int => int " where
  "r_l' == Global_Specification.r_l'"
abbreviation r_r' :: " int => int " where
  "r_r' == Global_Specification.r_r'"
abbreviation wordops__rotate_left' :: " [ int , int ] => int " where
  "wordops__rotate_left' == Global_Specification.rotate_left'"
abbreviation s_l' :: " int => int " where
  "s_l' == Global_Specification.s_l'"
abbreviation s_r' :: " int => int " where
  "s_r' == Global_Specification.s_r'"


abbreviation from_chain :: "chain' => chain" where
  "from_chain c == (
    word_of_int (h0'chain c),
    word_of_int (h1'chain c),
    word_of_int (h2'chain c),
    word_of_int (h3'chain c),
    word_of_int (h4'chain c))"

abbreviation from_chain_pair :: "chain_pair' => chain * chain" where
  "from_chain_pair cc == (
    from_chain (left'chain_pair cc),
    from_chain (right'chain_pair cc))"

abbreviation to_chain :: "chain => chain'" where
  "to_chain c ==
    (let (h0, h1, h2, h3, h4) = c in
      chain___default_rcd''
      (|h0'chain := uint h0,
        h1'chain := uint h1,
        h2'chain := uint h2,
        h3'chain := uint h3,
        h4'chain := uint h4|))"

abbreviation to_chain_pair :: "chain * chain => chain_pair'" where
  "to_chain_pair c == (let (c1, c2) = c in
    (| left'chain_pair = to_chain c1,
      right'chain_pair = to_chain c2 |))"

abbreviation steps' :: "[chain_pair', int, block'] => chain_pair'" where
  "steps' cc i b == to_chain_pair (steps
    (%n. word_of_int (b (int n)))
    (from_chain_pair cc)
    (nat i))"

abbreviation round' :: " [ chain' , block' ] => chain' " where
  "round' c b == to_chain (round (%n. word_of_int (b (int n))) (from_chain c))"

end
