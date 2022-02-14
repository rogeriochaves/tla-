------------------------------ MODULE Helpers ------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets

(* Helper to convert Sequence to Set *)
SeqToSet(s) == 
  LET F[i \in 0..Len(s)] == 
        IF i = 0 THEN {}
                 ELSE F[i-1] \union {s[i]}
  IN F[Len(s)]
  
IsInjective(s) ==
   \A i, j \in DOMAIN s: (s[i] = s[j]) => (i = j)
  
(* Helper to convert Set to Sequence *)
SetToSeq(S) ==
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
  

=============================================================================
\* Modification History
\* Last modified Thu Feb 03 22:13:37 CET 2022 by rchavesferna
\* Created Thu Feb 03 22:12:25 CET 2022 by rchavesferna
