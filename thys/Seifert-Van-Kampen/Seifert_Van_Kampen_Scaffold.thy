theory Seifert_Van_Kampen_Scaffold
  imports Pushout_Scaffold Carrier_Amalgamated_Free_Product
begin

section \<open>Conditional Seifert--van Kampen interface\<close>

text \<open>
  This theory packages a general quotient-level Seifert--van Kampen argument
  behind explicit encode/decode obligations. Once a decoding map factors
  through the full amalgamation quotient, and once the usual round-trip laws
  are available, the quotient-level bijection follows abstractly.
\<close>

locale svk_encode_decode_interface =
  fixes i1 :: "'h => 'a::group_add"
    and i2 :: "'h => 'b::group_add"
    and encode :: "'pi1_pushout =>
      ('a, 'b) free_product_word"
    and decode :: "('a, 'b) free_product_word => 'pi1_pushout"
  assumes decode_respects:
      "full_amalg_equiv i1 i2 u v ==> decode u = decode v"
    and decode_encode:
      "decode (encode x) = x"
    and encode_decode:
      "full_amalg_equiv i1 i2 (encode (decode w)) w"
begin

definition svk_quotient_map ::
  "'pi1_pushout => (('a, 'b) free_product_word) set"
where
  "svk_quotient_map x = full_amalg_class i1 i2 (encode x)"

lemma svk_quotient_map_in_space:
  "svk_quotient_map x \<in> full_amalgamated_free_product_space i1 i2"
  unfolding svk_quotient_map_def by (rule full_amalg_class_in_space)

lemma svk_quotient_map_injective:
  assumes "svk_quotient_map x = svk_quotient_map y"
  shows "x = y"
proof -
  have "full_amalg_equiv i1 i2 (encode x) (encode y)"
    using assms
    unfolding svk_quotient_map_def
    by (simp add: full_amalg_class_eq_iff)
  then have "decode (encode x) = decode (encode y)"
    by (rule decode_respects)
  then show ?thesis
    by (simp add: decode_encode)
qed

lemma svk_quotient_map_surjective:
  assumes "Q \<in> full_amalgamated_free_product_space i1 i2"
  shows "\<exists>x. svk_quotient_map x = Q"
proof -
  from assms obtain w where Q_rep: "Q = full_amalg_class i1 i2 w"
    unfolding full_amalgamated_free_product_space_def quotient_space_def full_amalg_class_def
    by blast
  have "svk_quotient_map (decode w) = Q"
    unfolding svk_quotient_map_def Q_rep
    by (simp add: full_amalg_class_eq_iff encode_decode)
  then show ?thesis
    by blast
qed

theorem seifert_van_kampen_bij_betw:
  "bij_betw svk_quotient_map UNIV (full_amalgamated_free_product_space i1 i2)"
  unfolding bij_betw_def
proof
  show "inj_on svk_quotient_map UNIV"
    unfolding inj_on_def
    using svk_quotient_map_injective by blast
next
  show "svk_quotient_map ` UNIV = full_amalgamated_free_product_space i1 i2"
  proof
    show "svk_quotient_map ` UNIV \<subseteq> full_amalgamated_free_product_space i1 i2"
      using svk_quotient_map_in_space by blast
  next
    show "full_amalgamated_free_product_space i1 i2 \<subseteq> svk_quotient_map ` UNIV"
      using svk_quotient_map_surjective by blast
  qed
qed

end

locale carrier_svk_encode_decode_interface =
  fixes G1 :: "'a set"
    and G2 :: "'b set"
    and H :: "'h set"
    and i1 :: "'h => 'a"
    and i2 :: "'h => 'b"
    and mult1 :: "'a => 'a => 'a"
    and one1 :: "'a"
    and mult2 :: "'b => 'b => 'b"
    and one2 :: "'b"
    and encode :: "'pi1_pushout => ('a, 'b) free_product_word"
    and decode :: "('a, 'b) free_product_word => 'pi1_pushout"
  assumes encode_in_space:
      "fpw_in_space G1 G2 (encode x)"
    and decode_respects:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v ==> decode u = decode v"
    and decode_encode:
      "decode (encode x) = x"
    and encode_decode:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (encode (decode w)) w"
begin

definition carrier_svk_quotient_map ::
  "'pi1_pushout => (('a, 'b) free_product_word) set"
where
  "carrier_svk_quotient_map x =
    carrier_full_amalg_class G1 G2 H i1 i2 mult1 one1 mult2 one2 (encode x)"

lemma carrier_svk_quotient_map_in_space:
  "carrier_svk_quotient_map x \<in>
    carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  unfolding carrier_svk_quotient_map_def
  by (rule carrier_full_amalg_class_in_space[OF encode_in_space])

lemma carrier_svk_quotient_map_injective:
  assumes "carrier_svk_quotient_map x = carrier_svk_quotient_map y"
  shows "x = y"
proof - 
  have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 (encode x) (encode y)"
    using assms
    unfolding carrier_svk_quotient_map_def
    by (simp add: carrier_full_amalg_class_eq_iff)
  then have "decode (encode x) = decode (encode y)"
    by (rule decode_respects)
  then show ?thesis
    by (simp add: decode_encode)
qed

lemma carrier_svk_quotient_map_surjective:
  assumes
    "Q \<in> carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  shows "\<exists>x. carrier_svk_quotient_map x = Q"
proof -
  from assms obtain w where
      "w \<in> carrier_fpw_space G1 G2"
      and Q_rep: "Q = carrier_full_amalg_class G1 G2 H i1 i2 mult1 one1 mult2 one2 w"
    unfolding carrier_full_amalgamated_free_product_space_def
    by blast
  have "carrier_svk_quotient_map (decode w) = Q"
    unfolding carrier_svk_quotient_map_def Q_rep
    by (simp add: carrier_full_amalg_class_eq_iff encode_decode)
  then show ?thesis
    by blast
qed

theorem carrier_seifert_van_kampen_bij_betw:
  "bij_betw carrier_svk_quotient_map UNIV
    (carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2)"
  unfolding bij_betw_def
proof
  show "inj_on carrier_svk_quotient_map UNIV"
    unfolding inj_on_def
    using carrier_svk_quotient_map_injective by blast
next
  show "carrier_svk_quotient_map ` UNIV =
      carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
  proof
    show "carrier_svk_quotient_map ` UNIV \<subseteq>
        carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2"
      using carrier_svk_quotient_map_in_space by blast
  next
    show "carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2
        \<subseteq> carrier_svk_quotient_map ` UNIV"
      using carrier_svk_quotient_map_surjective by blast
  qed
qed

end

end
