theory FIPS198_1
  imports  Words
           PKCS1v2_2_Interpretations
          
begin

text \<open>
https://csrc.nist.gov/publications/detail/fips/198/1/final
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.198-1.pdf

In this theory, we exactly translate the NIST standard for HMAC, found in FIPS 198-1 at the links
above.  We adhere as closely to the written standard as possible, including the variable names.
From the standard:

"This Standard specifies an algorithm for applications requiring message authentication. Message
authentication is achieved via the construction of a message authentication code (MAC). MACs based
on cryptographic hash functions are known as HMACs.

The purpose of a MAC is to authenticate both the source of a message and its integrity without the
use of any additional mechanisms. HMACs have two functionally distinct parameters, a message input
and a secret key known only to the message originator and intended receiver(s). Additional
applications of keyed-hash functions include their use in challenge-response identification
protocols for computing responses, which are a function of both a secret key and a challenge
message.

An HMAC function is used by the message sender to produce a value (the MAC) that is formed by
condensing the secret key and the message input. The MAC is typically sent to the message receiver
along with the message. The receiver computes the MAC on the received message using the same key
and HMAC function as were used by the sender, and compares the result computed with the received 
MAC. If the two values match, the message has been correctly received, and the receiver is assured
that the sender is a member of the community of users that share the key."

"HMAC uses the following parameters:
B      Block size (in bytes) of the input to the Approved hash function.
H      An Approved hash function.
ipad   Inner pad; the byte x‘36’ repeated B times.
K      Secret key shared between the originator and the intended receiver(s).
K0     The key K after any necessary pre-processing to form a B byte key.
L      Block size (in bytes) of the output of the Approved hash function.
opad   Outer pad; the byte x‘5c’ repeated B times.
text   The data on which the HMAC is calculated; text does not include the padded key.
       The length of text is n bits, where 0 \<le> n < 2^B - 8B."

While not explicitly stated, it is assumed that L < B.  It probably would not be a very good 
cryptographic hash if the output length (in bytes) L were equal to or larger than the block
size (in bytes) B.  These values for the hash algorithms found in FIPS 180 are:

Algorithm    Block Size          B    Message Digest Size         L
              (in bits)                    (in bits)               
SHA-1            512            64             160               20
SHA-224          512            64             224               28
SHA-256          512            64             256               32
SHA-384         1024           128             384               48
SHA-512         1024           128             512               64
SHA-512/224     1024           128             224               28
SHA-512/256     1024           128             256               32

In all these cases, L < B.  This is also true for the other Approved hash functions.  We include
this condition explicitly in the assumptions below.

Note that this standard uses the word "bytes" to refer to 8-bit values.  In other NIST standards,
they use the term "octets" for "bytes".  In this Isabelle translation, we use "octets".\<close>

section \<open>Definition\<close>

locale HMAC = 
  fixes   H   ::  "octets \<Rightarrow> octets"
  and     B L ::   nat
  assumes Hlen:   "\<forall>x. length (H x) = L"
  and     LlessB: "L < B"
begin
         
definition ipad :: octets where
  "ipad = replicate B 0x36"

definition opad :: octets where
  "opad = replicate B 0x5c"

definition computeK0 :: "octets \<Rightarrow> octets" where
  "computeK0 K = 
   (  let l = length K in
     ( if l = B then K else (
       if l > B then (H K) @ (replicate (B-L) 0) else (
                        K  @ (replicate (B-l) 0)
     )))
   )" 

lemma K0_len: "length (computeK0 K) = B" 
proof-
  let ?l = "length (computeK0 K)"
  have 1: "?l = B \<longrightarrow> ?thesis"  using computeK0_def by argo
  have 2: "?l > B \<longrightarrow> ?thesis"         
    by (smt (verit, ccfv_threshold) le_add_diff_inverse le_eq_less_or_eq length_append 
            length_replicate not_less computeK0_def Hlen LlessB) 
  have 3: "?l < B \<longrightarrow> ?thesis"        
    by (smt (verit, ccfv_threshold) le_add_diff_inverse le_eq_less_or_eq length_append 
            length_replicate not_less computeK0_def Hlen LlessB) 
  show ?thesis  using 1 2 3 by fastforce
qed

definition HMAC :: "octets \<Rightarrow> octets \<Rightarrow> octets" where
  "HMAC K text = 
  ( let K0 = computeK0 K in
    H ( (xor_octets K0 opad) @ (H ((xor_octets K0 ipad) @ text)) ) 
  )" 

lemma HMAC_len: "length (HMAC K text) = L"
  by (metis Hlen HMAC_def) 

end (* of the HMAC locale *)

section \<open>Interpretations\<close>

text \<open>The HMAC uses an approved hash function.  Many approved hash functions maybe be found in
the Secure Hash Standard, FIPS 180.  Here we interpret the HMAC locale (that is, define HMAC-SHA*)
for all the hash algorithms (SHA*) found in FIPS 180-4.\<close>

global_interpretation HMAC_SHA1_loc: HMAC SHA1octets 64 20
  defines HMAC_SHA1            = "HMAC_SHA1_loc.HMAC"
  and     HMAC_SHA1_ipad       = "HMAC_SHA1_loc.ipad"
  and     HMAC_SHA1_opad       = "HMAC_SHA1_loc.opad"
  and     HMAC_SHA1_computeK0  = "HMAC_SHA1_loc.computeK0"
proof -
  have "(20::nat) < 64" by simp 
  then show "HMAC SHA1octets 64 20" using SHA1octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA224_loc: HMAC SHA224octets 64 28
  defines HMAC_SHA224            = "HMAC_SHA224_loc.HMAC"
  and     HMAC_SHA224_ipad       = "HMAC_SHA224_loc.ipad"
  and     HMAC_SHA224_opad       = "HMAC_SHA224_loc.opad"
  and     HMAC_SHA224_computeK0  = "HMAC_SHA224_loc.computeK0"
proof -
  have "(28::nat) < 64" by simp 
  then show "HMAC SHA224octets 64 28" using SHA224octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA256_loc: HMAC SHA256octets 64 32
  defines HMAC_SHA256            = "HMAC_SHA256_loc.HMAC"
  and     HMAC_SHA256_ipad       = "HMAC_SHA256_loc.ipad"
  and     HMAC_SHA256_opad       = "HMAC_SHA256_loc.opad"
  and     HMAC_SHA256_computeK0  = "HMAC_SHA256_loc.computeK0"
proof -
  have "(32::nat) < 64" by simp 
  then show "HMAC SHA256octets 64 32" using SHA256octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA384_loc: HMAC SHA384octets 128 48
  defines HMAC_SHA384            = "HMAC_SHA384_loc.HMAC"
  and     HMAC_SHA384_ipad       = "HMAC_SHA384_loc.ipad"
  and     HMAC_SHA384_opad       = "HMAC_SHA384_loc.opad"
  and     HMAC_SHA384_computeK0  = "HMAC_SHA384_loc.computeK0"
proof -
  have "(48::nat) < 128" by simp 
  then show "HMAC SHA384octets 128 48" using SHA384octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA512_loc: HMAC SHA512octets 128 64
  defines HMAC_SHA512            = "HMAC_SHA512_loc.HMAC"
  and     HMAC_SHA512_ipad       = "HMAC_SHA512_loc.ipad"
  and     HMAC_SHA512_opad       = "HMAC_SHA512_loc.opad"
  and     HMAC_SHA512_computeK0  = "HMAC_SHA512_loc.computeK0"
proof -
  have "(64::nat) < 128" by simp 
  then show "HMAC SHA512octets 128 64" using SHA512octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA512_224_loc: HMAC SHA512_224octets 128 28
  defines HMAC_SHA512_224            = "HMAC_SHA512_224_loc.HMAC"
  and     HMAC_SHA512_224_ipad       = "HMAC_SHA512_224_loc.ipad"
  and     HMAC_SHA512_224_opad       = "HMAC_SHA512_224_loc.opad"
  and     HMAC_SHA512_224_computeK0  = "HMAC_SHA512_224_loc.computeK0"
proof -
  have "(28::nat) < 128" by simp 
  then show "HMAC SHA512_224octets 128 28" using SHA512_224octets_len HMAC_def by blast
qed

global_interpretation HMAC_SHA512_256_loc: HMAC SHA512_256octets 128 32
  defines HMAC_SHA512_256            = "HMAC_SHA512_256_loc.HMAC"
  and     HMAC_SHA512_256_ipad       = "HMAC_SHA512_256_loc.ipad"
  and     HMAC_SHA512_256_opad       = "HMAC_SHA512_256_loc.opad"
  and     HMAC_SHA512_256_computeK0  = "HMAC_SHA512_256_loc.computeK0"
proof -
  have "(32::nat) < 128" by simp 
  then show "HMAC SHA512_256octets 128 32" using SHA512_256octets_len HMAC_def by blast
qed

end
