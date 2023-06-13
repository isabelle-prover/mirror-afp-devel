theory PKCS1v2_2_Interpretations
  imports PKCS1v2_2
          FIPS180_4
          "HOL-Library.Code_Target_Numeral"

begin

text \<open>In this theory, we "interpret" or "instantiate" functions and schemes in PKCS1v2_2.thy that
rely on a hash function.  PKCS #1 does not specify any hash functions.  FIPS 180-4, the Secure Hash
Standard, defines several hash functions.\<close>


section \<open>SHA\<close>

text \<open>We will need a hash function to interpret many of the locales in PKCS #1.  PKCS #1 operates
on "octets" (8-bit bytes), so we will use the "octets versions" of the hash algorithms that are
defined in the last section of FIPS180_4.  Recall that PKCS #1 specifies the hash output when the
empty string (of octets) is input.  We show that those values actually are the correct result 
of hashing the empty input for each of the secure hashes.\<close>

lemma SHA1octets_empty [simp]:   "SHA1octets   [] = PKCS1_emptyL_lHash tSHA1"
  by eval

lemma SHA224octets_empty [simp]: "SHA224octets [] = PKCS1_emptyL_lHash tSHA224"
  by eval

lemma SHA256octets_empty [simp]: "SHA256octets [] = PKCS1_emptyL_lHash tSHA256"
  by eval

lemma SHA384octets_empty [simp]: "SHA384octets [] = PKCS1_emptyL_lHash tSHA384"
  by eval

lemma SHA512octets_empty [simp]: "SHA512octets [] = PKCS1_emptyL_lHash tSHA512"
  by eval

lemma SHA512_224octets_empty [simp]: "SHA512_224octets [] = PKCS1_emptyL_lHash tSHA512_224"
  by eval

lemma SHA512_256octets_empty [simp]: "SHA512_256octets [] = PKCS1_emptyL_lHash tSHA512_256"
  by eval

section \<open>MGF1\<close>

text \<open>The Mask Generating Function MGF1 defined in the appendix of PKCS #1 needs a hash function.
Here we "instantiate" MGF1 with all the secure hash algorithms defined in FIPS 180-4.  For each 
"instantiation" we prove "the output is valid" and "the output is the desire input length" lemmas.\<close>

subsection \<open>with SHA-1\<close>

definition MGF1wSHA1 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA1 mgfSeed maskLen = PKCS1_MGF1 SHA1octets SHA1_hLen mgfSeed maskLen"

lemma MGF1wSHA1_valid: "\<forall>x y. octets_valid (MGF1wSHA1 x y)"
  using SHA1octets_valid2 MGF1_valid MGF1wSHA1_def by presburger

lemma MGF1wSHA1_len: "\<forall>x y. length (MGF1wSHA1 x y) = y"
proof - 
  have "\<forall>x. length (SHA1octets x) = 20" using SHA1octets_len2 by satx
  then show ?thesis                     using MGF1wSHA1_def MGF1_len SHA1_hLen_def by simp
qed


subsection \<open>with SHA-224\<close>

definition MGF1wSHA224 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA224 mgfSeed maskLen = PKCS1_MGF1 SHA224octets SHA224_hLen mgfSeed maskLen"

lemma MGF1wSHA224_valid: "\<forall>x y. octets_valid (MGF1wSHA224 x y)"
  using SHA224octets_valid2 MGF1_valid MGF1wSHA224_def by presburger

lemma MGF1wSHA224_len: "\<forall>x y. length (MGF1wSHA224 x y) = y"
proof - 
  have "\<forall>x. length (SHA224octets x) = 28" using SHA224octets_len2 by satx
  then show ?thesis                       using MGF1wSHA224_def MGF1_len SHA224_hLen_def by simp
qed


subsection \<open>with SHA-256\<close>

definition MGF1wSHA256 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA256 mgfSeed maskLen = PKCS1_MGF1 SHA256octets SHA256_hLen mgfSeed maskLen"

lemma MGF1wSHA256_valid: "\<forall>x y. octets_valid (MGF1wSHA256 x y)"
  using SHA256octets_valid2 MGF1_valid MGF1wSHA256_def by presburger

lemma MGF1wSHA256_len: "\<forall>x y. length (MGF1wSHA256 x y) = y"
proof - 
  have "\<forall>x. length (SHA256octets x) = 32" using SHA256octets_len2 by satx
  then show ?thesis                       using MGF1wSHA256_def MGF1_len SHA256_hLen_def by simp
qed


subsection \<open>with SHA-384\<close>

definition MGF1wSHA384 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA384 mgfSeed maskLen = PKCS1_MGF1 SHA384octets SHA384_hLen mgfSeed maskLen"

lemma MGF1wSHA384_valid: "\<forall>x y. octets_valid (MGF1wSHA384 x y)"
  using SHA384octets_valid2 MGF1_valid MGF1wSHA384_def by presburger

lemma MGF1wSHA384_len: "\<forall>x y. length (MGF1wSHA384 x y) = y"
proof - 
  have "\<forall>x. length (SHA384octets x) = 48" using SHA384octets_len2 by satx
  then show ?thesis                       using MGF1wSHA384_def MGF1_len SHA384_hLen_def by simp
qed


subsection \<open>with SHA-512\<close>

definition MGF1wSHA512 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA512 mgfSeed maskLen = PKCS1_MGF1 SHA512octets SHA512_hLen mgfSeed maskLen"

lemma MGF1wSHA512_valid: "\<forall>x y. octets_valid (MGF1wSHA512 x y)"
  using SHA512octets_valid2 MGF1_valid MGF1wSHA512_def by presburger

lemma MGF1wSHA512_len: "\<forall>x y. length (MGF1wSHA512 x y) = y"
proof - 
  have "\<forall>x. length (SHA512octets x) = 64" using SHA512octets_len2 by satx
  then show ?thesis                       using MGF1wSHA512_def MGF1_len SHA512_hLen_def by simp
qed


subsection \<open>with SHA-512/224\<close>

definition MGF1wSHA512_224 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA512_224 mgfSeed maskLen = PKCS1_MGF1 SHA512_224octets SHA512_224_hLen mgfSeed maskLen"

lemma MGF1wSHA512_224_valid: "\<forall>x y. octets_valid (MGF1wSHA512_224 x y)"
  using SHA512_224octets_valid2 MGF1_valid MGF1wSHA512_224_def by presburger

lemma MGF1wSHA512_224_len: "\<forall>x y. length (MGF1wSHA512_224 x y) = y"
proof - 
  have "\<forall>x. length (SHA512_224octets x) = 28"   using SHA512_224octets_len2 by satx
  then show ?thesis  using MGF1wSHA512_224_def MGF1_len SHA512_224_hLen_def by simp
qed


subsection \<open>with SHA-512/256\<close>

definition MGF1wSHA512_256 :: "octets \<Rightarrow> nat \<Rightarrow> octets" where
  "MGF1wSHA512_256 mgfSeed maskLen = PKCS1_MGF1 SHA512_256octets SHA512_256_hLen mgfSeed maskLen"

lemma MGF1wSHA512_256_valid: "\<forall>x y. octets_valid (MGF1wSHA512_256 x y)"
  using SHA512_256octets_valid2 MGF1_valid MGF1wSHA512_256_def by presburger

lemma MGF1wSHA512_256_len: "\<forall>x y. length (MGF1wSHA512_256 x y) = y"
proof - 
  have "\<forall>x. length (SHA512_256octets x) = 32"   using SHA512_256octets_len2 by satx
  then show ?thesis  using MGF1wSHA512_256_def MGF1_len SHA512_256_hLen_def by simp
qed


section \<open>EMSA-PSS\<close>

text \<open>The encoding method EMSA-PSS, which is used for the signature scheme RSASSA-PSS, requires
a mask generating function and a hash function.  Note that you can "instantiate" MGF1 with SHA-X
and then use SHA-Y in the EMSA-PSS definition.  The examples we have from NIST use the same hash
algorithm for MGF1 and also in EMSA-PSS.  The examples we have from Wycheproof may use different
X and Y.\<close>

subsection \<open>with MGF1-SHA1 and SHA1\<close>

global_interpretation EMSA_PSS_SHA1: EMSA_PSS MGF1wSHA1 SHA1octets 20
  defines SHA1_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode"
  and     SHA1_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA1_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA1_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_H"
  and     SHA1_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA1_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA1_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA1_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA1_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA1_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA1_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_H"
  and     SHA1_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA1_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA1_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA1_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA1_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA1_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA1_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA1.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA1 x y)" using MGF1wSHA1_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA1 x y) = y"   using MGF1wSHA1_len by blast   
  have 3: "\<forall>x. octets_valid (SHA1octets x)"    using SHA1octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA1octets x) = 20"     using SHA1octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA1 SHA1octets 20"   by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA224 and SHA224\<close>

global_interpretation EMSA_PSS_SHA224: EMSA_PSS MGF1wSHA224 SHA224octets 28
  defines SHA224_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode"
  and     SHA224_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA224_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA224_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_H"
  and     SHA224_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA224_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA224_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA224_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA224_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA224_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA224_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_H"
  and     SHA224_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA224_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA224_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA224_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA224_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA224_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA224_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA224.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA224 x y)" using MGF1wSHA224_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA224 x y) = y"   using MGF1wSHA224_len by blast   
  have 3: "\<forall>x. octets_valid (SHA224octets x)"    using SHA224octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA224octets x) = 28"     using SHA224octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA224 SHA224octets 28" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA256 and SHA256\<close>

global_interpretation EMSA_PSS_SHA256: EMSA_PSS MGF1wSHA256 SHA256octets 32
  defines SHA256_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode"
  and     SHA256_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA256_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA256_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_H"
  and     SHA256_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA256_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA256_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA256_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA256_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA256_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA256_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_H"
  and     SHA256_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA256_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA256_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA256_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA256_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA256_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA256_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA256.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA256 x y)" using MGF1wSHA256_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA256 x y) = y"   using MGF1wSHA256_len by blast   
  have 3: "\<forall>x. octets_valid (SHA256octets x)"    using SHA256octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA256octets x) = 32"     using SHA256octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA256 SHA256octets 32" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA384 and SHA384\<close>

global_interpretation EMSA_PSS_SHA384: EMSA_PSS MGF1wSHA384 SHA384octets 48
  defines SHA384_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode"
  and     SHA384_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA384_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA384_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_H"
  and     SHA384_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA384_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA384_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA384_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA384_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA384_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA384_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_H"
  and     SHA384_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA384_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA384_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA384_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA384_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA384_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA384_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA384.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA384 x y)" using MGF1wSHA384_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA384 x y) = y"   using MGF1wSHA384_len by blast   
  have 3: "\<forall>x. octets_valid (SHA384octets x)"    using SHA384octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA384octets x) = 48"     using SHA384octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA384 SHA384octets 48" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA512 and SHA512\<close>

global_interpretation EMSA_PSS_SHA512: EMSA_PSS MGF1wSHA512 SHA512octets 64
  defines SHA512_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode"
  and     SHA512_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA512_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA512_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_H"
  and     SHA512_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA512_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA512_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA512_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA512_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA512_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA512_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_H"
  and     SHA512_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA512_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA512_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA512_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA512_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA512_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA512_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA512.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA512 x y)" using MGF1wSHA512_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA512 x y) = y"   using MGF1wSHA512_len by blast   
  have 3: "\<forall>x. octets_valid (SHA512octets x)"    using SHA512octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA512octets x) = 64"     using SHA512octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA512 SHA512octets 64" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA512_224 and SHA512_224\<close>

global_interpretation EMSA_PSS_SHA512_224: EMSA_PSS MGF1wSHA512_224 SHA512_224octets 28
  defines SHA512_224_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_H"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA512_224_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_H"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA512_224_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA512_224.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA512_224 x y)"     using MGF1wSHA512_224_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA512_224 x y) = y"       using MGF1wSHA512_224_len by blast   
  have 3: "\<forall>x. octets_valid (SHA512_224octets x)"        using SHA512_224octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA512_224octets x) = 28"         using SHA512_224octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA512_224 SHA512_224octets 28" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA512_256 and SHA512_256\<close>

global_interpretation EMSA_PSS_SHA512_256: EMSA_PSS MGF1wSHA512_256 SHA512_256octets 32
  defines SHA512_256_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_H"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA512_256_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_H"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA512_256_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA512_256.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA512_256 x y)"     using MGF1wSHA512_256_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA512_256 x y) = y"       using MGF1wSHA512_256_len by blast   
  have 3: "\<forall>x. octets_valid (SHA512_256octets x)"        using SHA512_256octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA512_256octets x) = 32"         using SHA512_256octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA512_256 SHA512_256octets 32" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

subsection \<open>with MGF1-SHA1 and SHA224\<close>

text \<open>As said above, you can use a different hash algorithm when defining the mask generating
function and when instantiating this encoding scheme.  Here is an example where we use SHA-1 with
MGF1 and then use SHA-224 for the (rest of the) encoding scheme.\<close>

global_interpretation EMSA_PSS_SHA1_224: EMSA_PSS MGF1wSHA1 SHA224octets 28
  defines SHA1_224_PKCS1_EMSA_PSS_Encode            = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_inputValid = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_inputValid"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_M'         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_M'"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_H          = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_H"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_PS         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_PS"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_DB         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_DB"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_dbMask     = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_dbMask"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_maskedDB   = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_maskedDB"
  and     SHA1_224_PKCS1_EMSA_PSS_Encode_EM         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Encode_EM"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_maskedDB   = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_maskedDB"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_H          = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_H"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_dbMask     = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_dbMask"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_DB         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_DB"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_PS_0x01    = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_PS_0x01"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_salt       = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_salt"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_M'         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_M'"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify_H'         = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify_H'"
  and     SHA1_224_PKCS1_EMSA_PSS_Verify            = "EMSA_PSS_SHA1_224.PKCS1_EMSA_PSS_Verify"
proof - 
  have 1: "\<forall>x y. octets_valid (MGF1wSHA1 x y)" using MGF1wSHA1_valid by blast  
  have 2: "\<forall>x y. length (MGF1wSHA1 x y) = y"   using MGF1wSHA1_len by blast   
  have 3: "\<forall>x. octets_valid (SHA224octets x)"  using SHA224octets_valid2 by blast    
  have 4: "\<forall>x. length (SHA224octets x) = 28"   using SHA224octets_len2 by blast 
  show    "EMSA_PSS MGF1wSHA1 SHA224octets 28" by (simp add: 1 2 3 4 EMSA_PSS.intro)
qed

section \<open>EMSA v1.5\<close>

text \<open>The encoding method EMSA v1.5, which is used for the signature scheme RSASSA v1.5, requires
a hash function with an algorithmID.  The algorithm IDs are found in the appendix of PKCS #1.\<close>

subsection \<open>with SHA1\<close>

global_interpretation EMSA_v1_5_SHA1: EMSA_v1_5 SHA1octets 20 "PKCS1_AlgorithmID tSHA1"
  defines EMSA_v1_5_SHA1_Encode_inputValid = "EMSA_v1_5_SHA1.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA1_Encode            = "EMSA_v1_5_SHA1.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA1octets x)"                using SHA1octets_valid2 by blast
  have 2: "\<forall>x. length (SHA1octets x) = 20"                 using SHA1octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA1)"         using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA1octets 20 (PKCS1_AlgorithmID tSHA1)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA224\<close>

global_interpretation EMSA_v1_5_SHA224: EMSA_v1_5 SHA224octets 28 "PKCS1_AlgorithmID tSHA224"
  defines EMSA_v1_5_SHA224_Encode_inputValid = "EMSA_v1_5_SHA224.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA224_Encode            = "EMSA_v1_5_SHA224.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA224octets x)"                  using SHA224octets_valid2 by blast
  have 2: "\<forall>x. length (SHA224octets x) = 28"                   using SHA224octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA224)"           using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA224octets 28 (PKCS1_AlgorithmID tSHA224)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA256\<close>

global_interpretation EMSA_v1_5_SHA256: EMSA_v1_5 SHA256octets 32 "PKCS1_AlgorithmID tSHA256"
  defines EMSA_v1_5_SHA256_Encode_inputValid = "EMSA_v1_5_SHA256.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA256_Encode            = "EMSA_v1_5_SHA256.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA256octets x)"                  using SHA256octets_valid2 by blast
  have 2: "\<forall>x. length (SHA256octets x) = 32"                   using SHA256octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA256)"           using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA256octets 32 (PKCS1_AlgorithmID tSHA256)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA384\<close>

global_interpretation EMSA_v1_5_SHA384: EMSA_v1_5 SHA384octets 48 "PKCS1_AlgorithmID tSHA384"
  defines EMSA_v1_5_SHA384_Encode_inputValid = "EMSA_v1_5_SHA384.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA384_Encode            = "EMSA_v1_5_SHA384.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA384octets x)"                  using SHA384octets_valid2 by blast
  have 2: "\<forall>x. length (SHA384octets x) = 48"                   using SHA384octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA384)"           using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA384octets 48 (PKCS1_AlgorithmID tSHA384)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA512\<close>

global_interpretation EMSA_v1_5_SHA512: EMSA_v1_5 SHA512octets 64 "PKCS1_AlgorithmID tSHA512"
  defines EMSA_v1_5_SHA512_Encode_inputValid = "EMSA_v1_5_SHA512.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA512_Encode            = "EMSA_v1_5_SHA512.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA512octets x)"                  using SHA512octets_valid2 by blast
  have 2: "\<forall>x. length (SHA512octets x) = 64"                   using SHA512octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA512)"           using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA512octets 64 (PKCS1_AlgorithmID tSHA512)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA512_224\<close>

global_interpretation EMSA_v1_5_SHA512_224: EMSA_v1_5 SHA512_224octets 28 "PKCS1_AlgorithmID tSHA512_224"
  defines EMSA_v1_5_SHA512_224_Encode_inputValid = "EMSA_v1_5_SHA512_224.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA512_224_Encode            = "EMSA_v1_5_SHA512_224.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA512_224octets x)"                      using SHA512_224octets_valid2 by blast
  have 2: "\<forall>x. length (SHA512_224octets x) = 28"                       using SHA512_224octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA512_224)"               using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA512_224octets 28 (PKCS1_AlgorithmID tSHA512_224)" using 1 2 3 EMSA_v1_5.intro by simp
qed

subsection \<open>with SHA512_256\<close>

global_interpretation EMSA_v1_5_SHA512_256: EMSA_v1_5 SHA512_256octets 32 "PKCS1_AlgorithmID tSHA512_256"
  defines EMSA_v1_5_SHA512_256_Encode_inputValid = "EMSA_v1_5_SHA512_256.PKCS1_EMSA_v1_5_Encode_inputValid"
  and     EMSA_v1_5_SHA512_256_Encode            = "EMSA_v1_5_SHA512_256.PKCS1_EMSA_v1_5_Encode"
proof - 
  have 1: "\<forall>x. octets_valid (SHA512_256octets x)"                      using SHA512_256octets_valid2 by blast
  have 2: "\<forall>x. length (SHA512_256octets x) = 32"                       using SHA512_256octets_len2 by blast
  have 3: "octets_valid (PKCS1_AlgorithmID tSHA512_256)"               using PKCS1_AlgorithmID_Valid by blast
  show "EMSA_v1_5 SHA512_256octets 32 (PKCS1_AlgorithmID tSHA512_256)" using 1 2 3 EMSA_v1_5.intro by simp
qed

end