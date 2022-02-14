---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833104833030000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833104833031000 == 
Permutations(const_162833104833030000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:10:48 CEST 2021 by rchaves
