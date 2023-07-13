theory Test_Vectors
  imports  "PKCS1v2_2_Test_Vectors"
           "FIPS180_4_Test_Vectors"
           "FIPS198_1_Test_Vectors"
            "SEC1v2_0_Test_Vectors"

begin

text \<open>In this set of theories, we express well-known crytographic standards in the language of
Isabelle.  The standards we have translated so far are:

  FIPS 180-4   : NIST's Secure Hash Standard, rev 4.
  FIPS 186-4   : Only the elliptic curves over prime fields, i.e. NIST's "P-" curves
  FIPS 198-1   : NIST's The Keyed-Hash Message Authentication Code (HMAC Standard)
  PKCS #1 v2.2 : RSA Laboratories' RSA Cryptography Standard, version 2.2
  SEC1 v2.0    : SEC's Elliptic Curve Cryptography, version 2.0 

The intention is that these translations will be used to prove that any particular implementation
matches the relevant standard.  With that in mind, the overriding principle is to adhere as closely
as possible, given the syntax of HOL, to the written standard.  It should be obvious to any reader,
regardless of their past experience with Isabelle, that these translations exactly match the 
standards.  Thus we use the same function and variable names as in the written standards whenever
possible and explain in the comments the few times when that is not possible.

We want the users of these theories to have faith that errors were not made in the translations.
We do two things to achieve this.  First, in addition to translating a standard, we provide a
robust supporting theory that proves anything that one might wish to know about the primitives
that the standard defines.  For example, we prove that encryption and decryption are inverse 
operations.  We prove when RSA keys are equivalent.  We prove that if a message is signed, then
that signature and message will pass the verification operation.  Any fact that you may need in
using these standards, we hope and believe we have already proved for you.

Second, we prove (by evaluation) that the test vectors provided by NIST, et al, check as intended
(whether a passing or failing test case.)  The theories imported here are the test vector files
for all the translated standards.  We chose to run all the NIST test vectors that were available.
For the secure hash standard, this comes to just two test vectors for each hash size.  For other
standards, this means we run hundreds or thousands of test vectors.  Where the NIST test vectors
do not cover all sections of the standard, we find additional test vectors from Wycheproof.  The
bottom line is that some of these test vector files are quite large and it takes some time for
Isabelle to run through all of them.  For this reason, we segregate the test vector theories from 
the standards themselves for the times when the user only wants to use the standards.
\<close>
end