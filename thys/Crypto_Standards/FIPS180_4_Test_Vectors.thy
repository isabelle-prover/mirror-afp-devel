theory FIPS180_4_Test_Vectors
  imports FIPS180_4
          "HOL-Library.Code_Target_Numeral"

begin

text \<open> https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values

NIST provides test vectors for its cryptographic standards.  In this theory, we verify that the
implementation of FIPS 180-4 in FIPS180_4.thy produces the values given in the NIST examples.
There is a one-block and a two-block example for each hash algorithm.  In this theory we check
the final hash value, and not each intermediate value given in the NIST documentation.

The one-block message sample for every hash algorithm is "abc", the ASCII string represented by
the hex character string 0x616263.  The intended message has 3 bytes, or 24 bits where the high
bit is 0.  Similarly, the two-block sample messages are ASCII strings that begin with "a" = 0x61.
So the bit-length of all the sample messages is a multiple of 8 (either 24 or 448 or 896) where 
the highest bit of the message is zero.

For fun, we show that all the test vectors work for the secure has algorithms as functions on
natural numbers and also for the SHA*octets functions that operate on octet strings.  Note that
nat_to_octets is a quick way to turn the nat 0x616263 into the list of nats [0x61,0x62,0x63].  It
is particularly convenient when the input value has many more than 3 octets.  Care needs to be 
taken if the message starts with the octet 0x00.  This does not occur in these test vectors.
\<close>
 
section \<open>SHA-1\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA1.pdf\<close>

lemma SHA1_OneBlockMessageSample:
  "SHA1 0x616263 24 = 0xA9993E364706816ABA3E25717850C26C9CD0D89D"
  by eval

lemma SHA1_TwoBlockMessageSample:
  "SHA1 
   0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071 
   448 
   = 0x84983E441C3BD26EBAAE4AA1F95129E5E54670F1"
  by eval

lemma SHA1_OneBlockMessageSample_octets:
  "SHA1octets (nat_to_octets 0x616263) 
             = nat_to_octets 0xA9993E364706816ABA3E25717850C26C9CD0D89D"
  by eval

lemma SHA1_TwoBlockMessageSample_octets:
  "SHA1octets 
     (nat_to_octets 0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071)  
    = nat_to_octets 0x84983E441C3BD26EBAAE4AA1F95129E5E54670F1"
  by eval

section \<open>SHA-224\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA224.pdf\<close>

lemma SHA224_OneBlockMessageSample:
  "SHA224 0x616263 24 = 0x23097D223405D8228642A477BDA255B32AADBCE4BDA0B3F7E36C9DA7"
  by eval

lemma SHA224_TwoBlockMessageSample:
  "SHA224 
   0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071 
   448 
   = 0x75388B16512776CC5DBA5DA1FD890150B0C6455CB4F58B1952522525"
  by eval

lemma SHA224_OneBlockMessageSample_octets:
  "SHA224octets
    (nat_to_octets 0x616263) 
   = nat_to_octets 0x23097D223405D8228642A477BDA255B32AADBCE4BDA0B3F7E36C9DA7"
  by eval

lemma SHA224_TwoBlockMessageSample_octets:
  "SHA224octets 
    (nat_to_octets 0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071)
   = nat_to_octets 0x75388B16512776CC5DBA5DA1FD890150B0C6455CB4F58B1952522525"
  by eval

section \<open>SHA-256\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf\<close>

lemma SHA256_OneBlockMessageSample:
  "SHA256 0x616263 24 = 0xBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD"
  by eval

lemma SHA256_TwoBlockMessageSample:
  "SHA256 
   0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071 
   448 
   = 0x248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1"
  by eval

lemma SHA256_OneBlockMessageSample_octets:
  "SHA256octets (nat_to_octets 0x616263) 
               = nat_to_octets 0xBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD"
  by eval

lemma SHA256_TwoBlockMessageSample_octets:
  "SHA256octets 
    (nat_to_octets 0x6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f7071)
   = nat_to_octets 0x248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1"
  by eval

section \<open>SHA-384\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA384.pdf\<close>

lemma SHA384_OneBlockMessageSample:
  "SHA384 0x616263 24 = 0xCB00753F45A35E8BB5A03D699AC65007272C32AB0EDED1631A8B605A43FF5BED8086072BA1E7CC2358BAECA134C825A7"
  by eval

lemma SHA384_TwoBlockMessageSample:
  "SHA384 
   0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475
   896
   = 0x09330C33F71147E83D192FC782CD1B4753111B173B3B05D22FA08086E3B0F712FCC7C71A557E2DB966C3E9FA91746039"
  by eval

lemma SHA384_OneBlockMessageSample_octets:
  "SHA384octets (nat_to_octets 0x616263) 
               = nat_to_octets 0xCB00753F45A35E8BB5A03D699AC65007272C32AB0EDED1631A8B605A43FF5BED8086072BA1E7CC2358BAECA134C825A7"
  by eval

lemma SHA384_TwoBlockMessageSample_octets:
  "SHA384octets 
    (nat_to_octets 0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475)
   = nat_to_octets 0x09330C33F71147E83D192FC782CD1B4753111B173B3B05D22FA08086E3B0F712FCC7C71A557E2DB966C3E9FA91746039"
  by eval

section \<open>SHA-512\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf\<close>

lemma SHA512_OneBlockMessageSample:
  "SHA512 0x616263 24 = 0xDDAF35A193617ABACC417349AE20413112E6FA4E89A97EA20A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD454D4423643CE80E2A9AC94FA54CA49F"
  by eval

lemma SHA512_TwoBlockMessageSample:
  "SHA512 
   0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475
   896
   = 0x8E959B75DAE313DA8CF4F72814FC143F8F7779C6EB9F7FA17299AEADB6889018501D289E4900F7E4331B99DEC4B5433AC7D329EEB6DD26545E96E55B874BE909"
  by eval

lemma SHA512_OneBlockMessageSample_octets:
  "SHA512octets (nat_to_octets 0x616263) 
               = nat_to_octets 0xDDAF35A193617ABACC417349AE20413112E6FA4E89A97EA20A9EEEE64B55D39A2192992A274FC1A836BA3C23A3FEEBBD454D4423643CE80E2A9AC94FA54CA49F"
  by eval

lemma SHA512_TwoBlockMessageSample_octets:
  "SHA512octets 
    (nat_to_octets 0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475)
   = nat_to_octets 0x8E959B75DAE313DA8CF4F72814FC143F8F7779C6EB9F7FA17299AEADB6889018501D289E4900F7E4331B99DEC4B5433AC7D329EEB6DD26545E96E55B874BE909"
  by eval

section \<open>SHA-512/224\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512_224.pdf\<close>

lemma SHA512_224_OneBlockMessageSample:
  "SHA512_224 0x616263 24 = 0x4634270F707B6A54DAAE7530460842E20E37ED265CEEE9A43E8924AA"
  by eval

lemma SHA512_224_TwoBlockMessageSample:
  "SHA512_224 
   0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475
   896
   = 0x23FEC5BB94D60B23308192640B0C453335D664734FE40E7268674AF9"
  by eval

lemma SHA512_224_OneBlockMessageSample_octets:
  "SHA512_224octets (nat_to_octets 0x616263) 
                   = nat_to_octets 0x4634270F707B6A54DAAE7530460842E20E37ED265CEEE9A43E8924AA"
  by eval

lemma SHA512_224_TwoBlockMessageSample_octets:
  "SHA512_224octets 
    (nat_to_octets 0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475)
   = nat_to_octets 0x23FEC5BB94D60B23308192640B0C453335D664734FE40E7268674AF9"
  by eval

section \<open>SHA-512/256\<close>

text \<open>https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512_256.pdf\<close>

lemma SHA512_256_OneBlockMessageSample:
  "SHA512_256 0x616263 24 = 0x53048E2681941EF99B2E29B76B4C7DABE4C2D0C634FC6D46E0E2F13107E7AF23"
  by eval

lemma SHA512_256_TwoBlockMessageSample:
  "SHA512_256 
   0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475
   896
   = 0x3928E184FB8690F840DA3988121D31BE65CB9D3EF83EE6146FEAC861E19B563A"
  by eval

lemma SHA512_256_OneBlockMessageSample_octets:
  "SHA512_256octets (nat_to_octets 0x616263) 
                   = nat_to_octets 0x53048E2681941EF99B2E29B76B4C7DABE4C2D0C634FC6D46E0E2F13107E7AF23"
  by eval

lemma SHA512_256_TwoBlockMessageSample_octets:
  "SHA512_256octets 
    (nat_to_octets 0x61626364656667686263646566676869636465666768696a6465666768696a6b65666768696a6b6c666768696a6b6c6d6768696a6b6c6d6e68696a6b6c6d6e6f696a6b6c6d6e6f706a6b6c6d6e6f70716b6c6d6e6f7071726c6d6e6f707172736d6e6f70717273746e6f707172737475)
   = nat_to_octets 0x3928E184FB8690F840DA3988121D31BE65CB9D3EF83EE6146FEAC861E19B563A"
  by eval

end