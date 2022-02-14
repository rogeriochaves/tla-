---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833253143178000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833253143179000 == 
Permutations(const_162833253143178000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:35:31 CEST 2021 by rchaves
